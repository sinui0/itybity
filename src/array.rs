use core::slice::Iter as SliceIter;

use crate::{BitLength, FromBitIterator, GetBit, IntoBitIter, Lsb0, Msb0, ToBits};

impl<'a, T, const N: usize> ToBits<'a> for [T; N]
where
    &'a T: GetBit<Lsb0> + GetBit<Msb0> + BitLength + 'a,
{
    type IterLsb0 = IntoBitIter<SliceIter<'a, T>, Lsb0>;
    type IterMsb0 = IntoBitIter<SliceIter<'a, T>, Msb0>;

    fn iter_lsb0(&'a self) -> Self::IterLsb0 {
        IntoBitIter::from(self.iter())
    }

    fn iter_msb0(&'a self) -> Self::IterMsb0 {
        IntoBitIter::from(self.iter())
    }
}

impl<const N: usize, T> FromBitIterator for [T; N]
where
    T: FromBitIterator,
{
    fn from_lsb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
        let mut iter = iter.into_iter();
        core::array::from_fn(|_| T::from_lsb0_iter(iter.by_ref()))
    }

    fn from_msb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
        let mut iter = iter.into_iter();
        core::array::from_fn(|_| T::from_msb0_iter(iter.by_ref()))
    }
}
