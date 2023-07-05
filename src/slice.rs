use core::slice::Iter as SliceIter;

use crate::{BitLength, GetBit, IntoBitIter, Lsb0, Msb0, ToBits};

impl<'a, T> ToBits<'a> for [T]
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
