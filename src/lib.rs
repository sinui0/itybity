//! An itty bitty crate providing bit iterators and bit iterator accessories.
//!
//! No dependencies, no unsafe, and `#![no_std]` compatible.
//!
//! # Summary
//!
//! This crate provides iterators for iterating over the bits of various types, including integers, slices, and strings.
//! These iterators can be conveniently accessed via the provided extension traits, eg [`ToBits`], [`IntoBits`], and [`StrToBits`].
//!
//! The [`FromBitIterator`] trait provides implementations for parsing types from bit iterators.
//!
//! # Performance
//!
//! This crate was not designed with performance in mind, but rather simplicity. For a more performant and memory
//! efficient alternative, see [`bitvec`](https://docs.rs/bitvec/latest/bitvec/).
//!
//! That being said, the iterators in this crate are still reasonably fast and compact.
//!
//! # Bit Order
//!
//! Be careful not to confuse bit order with byte order (endianness). Bit order refers to the order in which bits are positioned
//! within a container. See [this wiki](https://en.wikipedia.org/wiki/Bit_numbering) for more information.
//!
//! Conventionally, bits are written with the least-significant bit on the right. However, when dealing with bit vectors it is often
//! more intuitive to have the least-significant bit reside at index 0, ie left-most or Lsb0 order.
//!
//! For example, the number 69 in binary is `01000101`, which translates to the following bit vector in Lsb0:
//!
//! `[1, 0, 1, 0, 0, 0, 1, 0]`
//!
//! And the following in Msb0:
//!
//! `[0, 1, 0, 0, 0, 1, 0, 1]`
//!
//! # Usage
//!
//! First, add the following to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! itybity = "0.1"
//! ```
//!
//! # Examples
//!
//! ```rust
//! use itybity::{ToBits, IntoBits, FromBitIterator, StrToBits};
//!
//! let byte = 0b1010_1010u8;
//!
//! // Convert to a Vec<bool> in Lsb0 order.
//! let bits = byte.to_lsb0_vec();
//!
//! assert_eq!(bits, vec![false, true, false, true, false, true, false, true]);
//!
//! // Writing a bit vector using bools is a pain, use a string instead!
//! //
//! // Notice that the string is written in Msb0 order, and we reverse it to Lsb0.
//! let expected_bits = "10101010".iter_bits().rev().collect::<Vec<bool>>();
//!
//! assert_eq!(bits, expected_bits);
//!
//! // Convert back to a u8.
//! let new_byte = u8::from_lsb0_iter(bits);
//! assert_eq!(byte, new_byte);
//!
//! // We can work with slices too!
//! let bytes = vec![0u8, 1u8, 2u8, 3u8];
//!
//! // Create an iterator over the bits in Msb0 order.
//! let bits = bytes.iter_msb0();
//!
//! assert_eq!(bits.len(), 32);
//!
//! // Convert back to a different type
//! let data = u32::from_msb0_iter(bits);
//!
//! // If we have an iterator of values, we can map it to an iterator of bits.
//! let iter = vec![0u8, 1u8, 2u8, 3u8].into_iter();
//!
//! let bit_iter = iter.flat_map(IntoBits::into_iter_lsb0);
//!
//! // And we can parse it back
//! let values = Vec::<u8>::from_lsb0_iter(bit_iter);
//!
//! assert_eq!(values, vec![0u8, 1u8, 2u8, 3u8]);
//!
//! // We can do the same with arrays. Notice that the array is longer, so the last element
//! // will be 0.
//! let values = <[u8; 5]>::from_lsb0_iter(values.iter_lsb0());
//!
//! assert_eq!(values, [0u8, 1u8, 2u8, 3u8, 0u8]);
//! ```
//!
//! # Features
//!
//! `itybity` supports `#[no_std]` by disabling the default features.
//!
//! - `std`: Enables `alloc`, for use of `Vec` and `String` types.
//!
//! # License
//!
//! Licensed under either of
//!
//! * [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
//! * [MIT license](http://opensource.org/licenses/MIT)
//!
//! at your option.
//!
//! # Contribution
//!
//! Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in the work by you,
//! as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.

#![cfg_attr(not(test), no_std)]
#![deny(missing_docs, unreachable_pub, unused_must_use)]
#![deny(clippy::all)]
#![deny(unsafe_code)]

#[cfg(feature = "alloc")]
mod alloc;
mod array;
mod bool;
#[cfg(feature = "rayon")]
mod rayon;
mod slice;
mod str;
mod traits;
mod uint;

pub use self::str::StrBitIter;
pub use traits::{
    BitIterable, BitLength, BitOrder, FromBitIterator, GetBit, IntoBitIterator, IntoBits,
    StrToBits, ToBits,
};

#[cfg(feature = "rayon")]
pub use self::rayon::{
    IntoParallelBitIterator, IntoParallelBits, IntoParallelRefBitIterator, ParallelBitIter,
    ToParallelBits,
};

use core::{fmt::Debug, iter::FusedIterator, marker::PhantomData, ops::Range};

/// Lsb0 bit order.
#[derive(Debug, Clone, Copy)]
pub struct Lsb0;

/// Msb0 bit order.
#[derive(Debug, Clone, Copy)]
pub struct Msb0;

impl BitOrder for Lsb0 {}
impl BitOrder for Msb0 {}

/// Iterator over bits.
#[derive(Debug, Clone)]
pub struct BitIter<T, O>
where
    O: BitOrder,
{
    value: T,
    range: Range<usize>,
    bit_order: PhantomData<O>,
}

impl<T, O> Iterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        self.range.next().map(|i| self.value.get_bit(i))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl<T, O> ExactSizeIterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<T, O> DoubleEndedIterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range.next_back().map(|i| self.value.get_bit(i))
    }
}

impl<T, O> FusedIterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<T, O> From<T> for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn from(value: T) -> Self {
        Self {
            value,
            range: 0..T::BITS,
            bit_order: PhantomData,
        }
    }
}

/// A wrapper that converts an iterator over values to an iterator over bits.
pub struct IntoBitIter<I, O>
where
    I: Iterator,
    O: BitOrder,
{
    iter: I,
    next: Option<BitIter<I::Item, O>>,
    next_back: Option<BitIter<I::Item, O>>,
    bit_order: PhantomData<O>,
}

impl<I, O> IntoBitIter<I, O>
where
    I: Iterator,
    O: BitOrder,
{
    /// Returns a reference to the wrapped iterator.
    pub fn inner(&self) -> &I {
        &self.iter
    }

    /// Returns a mutable reference to the wrapped iterator.
    pub fn inner_mut(&mut self) -> &mut I {
        &mut self.iter
    }

    /// Returns the wrapped iterator.
    ///
    /// # Warning
    ///
    /// `IntoBitIter` buffers items from the wrapped iterator, so calling this method may
    /// cause data loss.
    pub fn into_inner(self) -> I {
        self.iter
    }
}

impl<I, O> Debug for IntoBitIter<I, O>
where
    I: Iterator + Debug,
    O: BitOrder,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IntoBitIter")
            .field("iter", &self.iter)
            .field("bit_order", &self.bit_order)
            .finish()
    }
}

impl<I, O> Clone for IntoBitIter<I, O>
where
    I: Iterator + Clone,
    I::Item: Clone,
    O: BitOrder,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            next: self.next.clone(),
            next_back: self.next_back.clone(),
            bit_order: self.bit_order,
        }
    }
}

impl<I, O> Iterator for IntoBitIter<I, O>
where
    I: Iterator,
    I::Item: GetBit<O> + BitLength,
    O: BitOrder,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item) = &mut self.next {
            if let Some(bit) = item.next() {
                return Some(bit);
            }
        }

        self.next = self.iter.next().map(BitIter::from);

        if self.next.is_some() {
            return self.next();
        }

        if let Some(item) = &mut self.next_back {
            if let Some(bit) = item.next() {
                return Some(bit);
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (mut lower, mut upper) = self.iter.size_hint();

        lower = lower.saturating_mul(I::Item::BITS);
        upper = upper.map(|u| u.saturating_mul(I::Item::BITS));

        if let Some(item) = &self.next {
            let remaining = item.range.len();
            lower = lower.saturating_add(remaining);
            upper = upper.map(|u| u.saturating_add(remaining));
        }

        if let Some(item) = &self.next_back {
            let remaining = item.range.len();
            lower = lower.saturating_add(remaining);
            upper = upper.map(|u| u.saturating_add(remaining));
        }

        (lower, upper)
    }
}

impl<I, O> DoubleEndedIterator for IntoBitIter<I, O>
where
    I: DoubleEndedIterator,
    I::Item: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if let Some(item) = &mut self.next_back {
            if let Some(bit) = item.next_back() {
                return Some(bit);
            }
        }

        self.next_back = self.iter.next_back().map(BitIter::from);

        if self.next_back.is_some() {
            return self.next_back();
        }

        if let Some(item) = &mut self.next {
            if let Some(bit) = item.next_back() {
                return Some(bit);
            }
        }

        None
    }
}

impl<I, O> ExactSizeIterator for IntoBitIter<I, O>
where
    I: ExactSizeIterator,
    I::Item: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<I, O> From<I> for IntoBitIter<I, O>
where
    I: Iterator,
    I::Item: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn from(iter: I) -> Self {
        IntoBitIter {
            iter,
            next: None,
            next_back: None,
            bit_order: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::*;

    trait Fixtures<T> {
        const BITS: usize;
        const ZERO: T;
        const ONE: T;
        const TWO: T;
        const MAX: T;
    }

    macro_rules! impl_fixtures {
        ($($ty:ty),*) => {
            $(
                impl Fixtures<$ty> for $ty {
                    const BITS: usize = <$ty>::BITS as usize;
                    const ZERO: $ty = 0;
                    const ONE: $ty = 1;
                    const TWO: $ty = 2;
                    const MAX: $ty = <$ty>::MAX;
                }
            )*
        };
    }

    impl_fixtures!(u8, u16, u32, u64, u128, usize);

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_from_bits<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T> + FromBitIterator + PartialEq + std::fmt::Debug + std::fmt::Binary,
    {
        for value in [T::ZERO, T::ONE, T::TWO, T::MAX] {
            let msb0_bits = format!("{:0width$b}", value, width = T::BITS);
            let msb0_value = T::from_msb0_iter(msb0_bits.iter_bits());
            let lsb0_value = T::from_lsb0_iter(msb0_bits.iter_bits().rev());

            assert_eq!(msb0_value, value);
            assert_eq!(lsb0_value, value);
        }
    }

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_from_bits_array<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T>
            + IntoBits
            + FromBitIterator
            + BitLength
            + GetBit<Lsb0>
            + GetBit<Msb0>
            + PartialEq
            + std::fmt::Debug
            + std::fmt::Binary
            + Copy,
    {
        let expected_values = [T::ZERO, T::ONE, T::TWO, T::MAX];

        let lsb0 = <[T; 4]>::from_lsb0_iter(expected_values.into_iter_lsb0());
        let msb0 = <[T; 4]>::from_msb0_iter(expected_values.into_iter_msb0());

        assert_eq!(lsb0, expected_values);
        assert_eq!(msb0, expected_values);
    }

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_from_bits_vec<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T>
            + IntoBits
            + FromBitIterator
            + BitLength
            + GetBit<Lsb0>
            + GetBit<Msb0>
            + PartialEq
            + std::fmt::Debug
            + std::fmt::Binary
            + Copy,
    {
        let expected_values = [T::ZERO, T::ONE, T::TWO, T::MAX];

        let lsb0 = Vec::<T>::from_lsb0_iter(expected_values.into_iter_lsb0());
        let msb0 = Vec::<T>::from_msb0_iter(expected_values.into_iter_msb0());

        assert_eq!(lsb0, expected_values);
        assert_eq!(msb0, expected_values);
    }

    #[rstest]
    fn test_to_bit_iter_boolvec() {
        let bits = vec![false, true, false, true, false, true, false, true];

        assert_eq!(u8::from_lsb0_iter(bits.iter_lsb0()), 0b10101010);
    }

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_to_bit_iter<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T> + std::fmt::Binary,
        for<'a> T: ToBits<'a>,
    {
        for value in [T::ZERO, T::ONE, T::TWO, T::MAX] {
            let expected_msb0_bits = format!("{:0width$b}", value, width = T::BITS).to_bit_vec();
            let expected_lsb0_bits = expected_msb0_bits
                .iter()
                .copied()
                .rev()
                .collect::<Vec<bool>>();

            assert_eq!(value.to_msb0_vec(), expected_msb0_bits);
            assert_eq!(value.to_lsb0_vec(), expected_lsb0_bits);
        }
    }

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_to_bit_iter_slice<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T> + std::fmt::Binary,
        for<'a> [T]: ToBits<'a>,
    {
        let expected_msb0_bits = format!(
            "{:0width$b}{:0width$b}{:0width$b}{:0width$b}",
            T::ZERO,
            T::ONE,
            T::TWO,
            T::MAX,
            width = T::BITS
        )
        .to_bit_vec();
        let expected_lsb0_bits = expected_msb0_bits
            .chunks(T::BITS)
            .flat_map(|chunk| chunk.iter().copied().rev())
            .collect::<Vec<bool>>();

        let slice = [T::ZERO, T::ONE, T::TWO, T::MAX];

        assert_eq!(slice.to_msb0_vec(), expected_msb0_bits);
        assert_eq!(slice.to_lsb0_vec(), expected_lsb0_bits);
    }
}
