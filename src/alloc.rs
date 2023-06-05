extern crate alloc;

use alloc::vec::{IntoIter, Vec};
use core::iter::FlatMap;

use crate::{BitIter, BitLength, GetBit, IntoBits, Lsb0, Msb0, ToBits};

impl<'a> ToBits<'a> for Vec<bool> {
    type IterLsb0 = core::iter::Copied<core::slice::Iter<'a, bool>>;
    type IterMsb0 = core::iter::Copied<core::slice::Iter<'a, bool>>;

    fn iter_lsb0(&'a self) -> Self::IterLsb0 {
        self.iter().copied()
    }

    fn iter_msb0(&'a self) -> Self::IterMsb0 {
        self.iter().copied()
    }
}

impl IntoBits for Vec<bool> {
    type IterLsb0 = IntoIter<bool>;
    type IterMsb0 = IntoIter<bool>;

    fn into_iter_lsb0(self) -> Self::IterLsb0 {
        self.into_iter()
    }

    fn into_iter_msb0(self) -> Self::IterMsb0 {
        self.into_iter()
    }
}

impl<T> IntoBits for Vec<T>
where
    T: BitLength + GetBit<Lsb0> + GetBit<Msb0>,
{
    type IterLsb0 = FlatMap<IntoIter<T>, BitIter<T, Lsb0>, fn(T) -> BitIter<T, Lsb0>>;
    type IterMsb0 = FlatMap<IntoIter<T>, BitIter<T, Msb0>, fn(T) -> BitIter<T, Msb0>>;

    fn into_iter_lsb0(self) -> Self::IterLsb0 {
        self.into_iter().flat_map(|elem| elem.into_iter_lsb0())
    }

    fn into_iter_msb0(self) -> Self::IterMsb0 {
        self.into_iter().flat_map(|elem| elem.into_iter_msb0())
    }
}
