#[cfg(feature = "alloc")]
extern crate alloc as core_alloc;

#[cfg(feature = "alloc")]
use core_alloc::vec::Vec;

use crate::{Lsb0, Msb0, StrBitIter};

/// Marker trait for bit order.
pub trait BitOrder: sealed::Sealed + Clone + Copy + Send + Sync + 'static {}

mod sealed {
    /// That's cool if you've invented some new bit order, but sry bruv, this trait is sealed.
    pub trait Sealed {}

    impl Sealed for super::Lsb0 {}
    impl Sealed for super::Msb0 {}
}

/// Trait for types with a const bit length.
pub trait BitLength {
    /// The bit length of the type.
    const BITS: usize;
}

impl<const N: usize, T> BitLength for [T; N]
where
    T: BitLength,
{
    const BITS: usize = N * T::BITS;
}

impl<const N: usize, T> BitLength for &[T; N]
where
    T: BitLength,
{
    const BITS: usize = N * T::BITS;
}

/// Trait for getting a bit at a given index.
pub trait GetBit<O>
where
    O: BitOrder,
{
    /// Returns the bit at the given index.
    ///
    /// # Panics
    ///
    /// Implementations may panic if the provided index is out of bounds.
    fn get_bit(&self, index: usize) -> bool;
}

impl<const N: usize, T, O> GetBit<O> for [T; N]
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn get_bit(&self, index: usize) -> bool {
        self[index / T::BITS].get_bit(index % T::BITS)
    }
}

impl<const N: usize, T, O> GetBit<O> for &[T; N]
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn get_bit(&self, index: usize) -> bool {
        self[index / T::BITS].get_bit(index % T::BITS)
    }
}

/// Trait used for parsing a value from a bit iterator.
pub trait FromBits {
    /// Parses a value from an iterator of bits in Lsb0 order.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields fewer than `Self::BITS` bits.
    fn from_lsb0(iter: impl IntoIterator<Item = bool>) -> Self;

    /// Parses a value from an iterator of bits in Msb0 order.
    ///
    /// # Panics
    ///
    /// Panics if the iterator yields fewer than `Self::BITS` bits.
    fn from_msb0(iter: impl IntoIterator<Item = bool>) -> Self;
}

impl<const N: usize, T> FromBits for [T; N]
where
    T: FromBits,
{
    fn from_lsb0(iter: impl IntoIterator<Item = bool>) -> Self {
        let mut iter = iter.into_iter();
        core::array::from_fn(|_| T::from_lsb0(iter.by_ref()))
    }

    fn from_msb0(iter: impl IntoIterator<Item = bool>) -> Self {
        let mut iter = iter.into_iter();
        core::array::from_fn(|_| T::from_msb0(iter.by_ref()))
    }
}

/// Trait for converting types into a borrowing bit iterator.
pub trait ToBits<'a> {
    /// The Lsb0 bit iterator type.
    type IterLsb0: Iterator<Item = bool> + 'a;
    /// The Msb0 bit iterator type.
    type IterMsb0: Iterator<Item = bool> + 'a;

    /// Returns a bit iterator over `self` in Lsb0 order.
    fn iter_lsb0(&'a self) -> Self::IterLsb0;

    /// Returns a bit vector of `self` in Lsb0 order.
    #[cfg(feature = "alloc")]
    fn to_lsb0_vec(&'a self) -> Vec<bool> {
        self.iter_lsb0().collect()
    }

    /// Returns a bit iterator over `self` in Msb0 order.
    fn iter_msb0(&'a self) -> Self::IterMsb0;

    /// Returns a bit vector of `self` in Msb0 order.
    #[cfg(feature = "alloc")]
    fn to_msb0_vec(&'a self) -> Vec<bool> {
        self.iter_msb0().collect()
    }
}

/// Trait for converting types into a bit iterator.
pub trait IntoBits: Sized {
    /// The Lsb0 bit iterator type.
    type IterLsb0: Iterator<Item = bool>;
    /// The Msb0 bit iterator type.
    type IterMsb0: Iterator<Item = bool>;

    /// Converts `self` into a bit iterator in Lsb0 order.
    fn into_iter_lsb0(self) -> Self::IterLsb0;

    /// Converts `self` into a bit vector in Lsb0 order.
    #[cfg(feature = "alloc")]
    fn into_lsb0_vec(self) -> Vec<bool> {
        self.into_iter_lsb0().collect()
    }

    /// Converts `self` into a bit iterator in Msb0 order.
    fn into_iter_msb0(self) -> Self::IterMsb0;

    /// Converts `self` into a bit vector in Msb0 order.
    #[cfg(feature = "alloc")]
    fn into_msb0_vec(self) -> Vec<bool> {
        self.into_iter_msb0().collect()
    }
}

/// Trait for converting bit strings into a bit iterator.
pub trait StrToBits<'a> {
    /// Converts a bit string into a bit iterator.
    ///
    /// The returned iterator will yield `true` for any **character** that is not `'0'`,
    fn iter_bits(&'a self) -> StrBitIter<'a>;

    /// Converts a bit string into a bit vector.
    ///
    /// The returned vector will contain `true` for any **character** that is not `'0'`,
    fn to_bit_vec(&'a self) -> Vec<bool> {
        self.iter_bits().collect()
    }
}
