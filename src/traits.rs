#[cfg(feature = "alloc")]
extern crate alloc as core_alloc;

#[cfg(feature = "alloc")]
use core_alloc::vec::Vec;

use crate::{str::StrBitIter, BitIter, IntoBitIter, Lsb0, Msb0};

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

impl<T: ?Sized> BitLength for &T
where
    T: BitLength,
{
    const BITS: usize = T::BITS;
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

impl<T: ?Sized, O> GetBit<O> for &T
where
    T: GetBit<O>,
    O: BitOrder,
{
    fn get_bit(&self, index: usize) -> bool {
        T::get_bit(*self, index)
    }
}

/// A type whose bits can be iterated over.
pub trait BitIterable: GetBit<Lsb0> + GetBit<Msb0> + BitLength {}

impl<T: ?Sized> BitIterable for &T where T: BitIterable {}

/// Trait used for parsing a value from a bit iterator.
pub trait FromBitIterator {
    /// Parses a value from an iterator of bits in Lsb0 order.
    ///
    /// If the iterator is shorter than the number of bits in the type, the remaining bits are
    /// assumed to be zero.
    fn from_lsb0_iter(iter: impl IntoIterator<Item = bool>) -> Self;

    /// Parses a value from an iterator of bits in Msb0 order.
    ///
    /// If the iterator is shorter than the number of bits in the type, the remaining bits are
    /// assumed to be zero.
    fn from_msb0_iter(iter: impl IntoIterator<Item = bool>) -> Self;
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

impl<'a, T> ToBits<'a> for T
where
    &'a T: GetBit<Lsb0> + GetBit<Msb0> + BitLength + 'a,
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

/// Trait for converting types into a bit iterator.
///
/// This trait is automatically implemented for all types that implement `GetBit` and
/// `BitLength`.
pub trait IntoBits {
    /// The Lsb0 bit iterator type.
    type IterLsb0: Iterator<Item = bool>;
    /// The Msb0 bit iterator type.
    type IterMsb0: Iterator<Item = bool>;

    /// Converts `self` into a bit iterator in Lsb0 order.
    fn into_iter_lsb0(self) -> Self::IterLsb0;

    /// Converts `self` into a bit vector in Lsb0 order.
    #[cfg(feature = "alloc")]
    fn into_lsb0_vec(self) -> Vec<bool>
    where
        Self: Sized,
    {
        self.into_iter_lsb0().collect()
    }

    /// Converts `self` into a bit iterator in Msb0 order.
    fn into_iter_msb0(self) -> Self::IterMsb0;

    /// Converts `self` into a bit vector in Msb0 order.
    #[cfg(feature = "alloc")]
    fn into_msb0_vec(self) -> Vec<bool>
    where
        Self: Sized,
    {
        self.into_iter_msb0().collect()
    }
}

impl<T> IntoBits for T
where
    T: GetBit<Lsb0> + GetBit<Msb0> + BitLength,
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

/// Trait for converting iterators over values into iterators over bits.
///
/// This trait is automatically implemented for all types that implement `IntoIterator` where
/// the item type implements `IntoBits`.
pub trait IntoBitIterator {
    /// The Lsb0 bit iterator type.
    type IterLsb0: Iterator<Item = bool>;
    /// The Msb0 bit iterator type.
    type IterMsb0: Iterator<Item = bool>;

    /// Converts `self` into a bit iterator in Lsb0 order.
    fn into_iter_lsb0(self) -> Self::IterLsb0;

    /// Converts `self` into a bit vector in Lsb0 order.
    #[cfg(feature = "alloc")]
    fn into_lsb0_vec(self) -> Vec<bool>
    where
        Self: Sized,
    {
        self.into_iter_lsb0().collect()
    }

    /// Converts `self` into a bit iterator in Msb0 order.
    fn into_iter_msb0(self) -> Self::IterMsb0;

    /// Converts `self` into a bit vector in Msb0 order.
    #[cfg(feature = "alloc")]
    fn into_msb0_vec(self) -> Vec<bool>
    where
        Self: Sized,
    {
        self.into_iter_msb0().collect()
    }
}

impl<T> IntoBitIterator for T
where
    T: IntoIterator,
    T::Item: GetBit<Lsb0> + GetBit<Msb0> + BitLength,
{
    type IterLsb0 = IntoBitIter<T::IntoIter, Lsb0>;
    type IterMsb0 = IntoBitIter<T::IntoIter, Msb0>;

    fn into_iter_lsb0(self) -> Self::IterLsb0 {
        IntoBitIter::from(self.into_iter())
    }

    fn into_iter_msb0(self) -> Self::IterMsb0 {
        IntoBitIter::from(self.into_iter())
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
    #[cfg(feature = "alloc")]
    fn to_bit_vec(&'a self) -> Vec<bool> {
        self.iter_bits().collect()
    }
}
