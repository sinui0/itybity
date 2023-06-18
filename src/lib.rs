//! An itty bitty crate providing bit iterators and bit iterator accessories.
//!
//! No dependencies, no unsafe, and `#![no_std]` compatible.
//!
//! # Summary
//!
//! This crate provides iterators for iterating over the bits of various types, including integers, slices, and strings.
//! These iterators can be conveniently accessed via the provided extension traits, eg [`ToBits`], [`IntoBits`], and [`StrToBits`].
//!
//! The [`FromBits`] trait provides implementations for parsing types from bit iterators.
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
//! use itybity::{ToBits, IntoBits, FromBits, StrToBits};
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
//! let new_byte = u8::from_lsb0(bits);
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
//! let data = u32::from_msb0(bits);
//!
//! // If we have an iterator of values, we can map it to an iterator of bits.
//! let iter = vec![0u8, 1u8, 2u8, 3u8].into_iter();
//!
//! let bit_iter = iter.flat_map(IntoBits::into_iter_lsb0);
//!
//! // And we can parse it back
//! let values = Vec::<u8>::from_lsb0(bit_iter);
//!
//! assert_eq!(values, vec![0u8, 1u8, 2u8, 3u8]);
//!
//! // We can do the same with arrays. Notice that the array is longer, so the last element
//! // will be 0.
//! let values = <[u8; 5]>::from_lsb0(values.iter_lsb0());
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
mod bool;
mod slice;
mod str;
mod traits;
mod uint;

pub use self::str::StrBitIter;
pub use slice::SliceBitIter;
pub use traits::{BitLength, BitOrder, FromBits, GetBit, IntoBits, StrToBits, ToBits};

use core::{iter::FusedIterator, marker::PhantomData};

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
    pos: usize,
    bit_order: PhantomData<O>,
}

impl<T> Copy for BitIter<T, Lsb0> where T: Clone + Copy {}
impl<T> Copy for BitIter<T, Msb0> where T: Clone + Copy {}

impl<T, O> Iterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < T::BITS {
            let bit = self.value.get_bit(self.pos);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = T::BITS - self.pos;
        (remaining, Some(remaining))
    }
}

impl<T, O> ExactSizeIterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<T, O> FusedIterator for BitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<'a, T> ToBits<'a> for T
where
    &'a T: BitLength + GetBit<Lsb0> + GetBit<Msb0> + 'a,
{
    type IterLsb0 = BitIter<&'a T, Lsb0>;
    type IterMsb0 = BitIter<&'a T, Msb0>;

    fn iter_lsb0(&'a self) -> Self::IterLsb0 {
        BitIter::from(self)
    }

    fn iter_msb0(&'a self) -> Self::IterMsb0 {
        BitIter::from(self)
    }
}

impl<T> IntoBits for T
where
    T: BitLength + GetBit<Lsb0> + GetBit<Msb0>,
{
    type IterLsb0 = BitIter<T, Lsb0>;
    type IterMsb0 = BitIter<T, Msb0>;

    fn into_iter_lsb0(self) -> Self::IterLsb0 {
        BitIter::from(self)
    }

    fn into_iter_msb0(self) -> Self::IterMsb0 {
        BitIter::from(self)
    }
}

impl<T, O> From<T> for BitIter<T, O>
where
    T: GetBit<O>,
    O: BitOrder,
{
    fn from(value: T) -> Self {
        Self {
            value,
            pos: 0,
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
        T: Fixtures<T> + FromBits + PartialEq + std::fmt::Debug + std::fmt::Binary,
    {
        for value in [T::ZERO, T::ONE, T::TWO, T::MAX] {
            let msb0_bits = format!("{:0width$b}", value, width = T::BITS);
            let msb0_value = T::from_msb0(msb0_bits.iter_bits());
            let lsb0_value = T::from_lsb0(msb0_bits.iter_bits().rev());

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
            + FromBits
            + BitLength
            + GetBit<Lsb0>
            + GetBit<Msb0>
            + PartialEq
            + std::fmt::Debug
            + std::fmt::Binary
            + Copy,
    {
        let expected_values = [T::ZERO, T::ONE, T::TWO, T::MAX];

        let lsb0 = <[T; 4]>::from_lsb0(expected_values.into_iter_lsb0());
        let msb0 = <[T; 4]>::from_msb0(expected_values.into_iter_msb0());

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
            + FromBits
            + BitLength
            + GetBit<Lsb0>
            + GetBit<Msb0>
            + PartialEq
            + std::fmt::Debug
            + std::fmt::Binary
            + Copy,
    {
        let expected_values = [T::ZERO, T::ONE, T::TWO, T::MAX];

        let lsb0 = Vec::<T>::from_lsb0(expected_values.into_iter_lsb0());
        let msb0 = Vec::<T>::from_msb0(expected_values.into_iter_msb0());

        assert_eq!(lsb0, expected_values);
        assert_eq!(msb0, expected_values);
    }

    #[rstest]
    fn test_to_bit_iter_boolvec() {
        let bits = vec![false, true, false, true, false, true, false, true];

        assert_eq!(u8::from_lsb0(bits.iter_lsb0()), 0b10101010);
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
