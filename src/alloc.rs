extern crate alloc;

use alloc::vec::{IntoIter, Vec};
use core::iter::FlatMap;

use crate::{BitIter, BitLength, BitOrder, FromBits, GetBit, IntoBits, Lsb0, Msb0};

impl<T, O> GetBit<O> for Vec<T>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn get_bit(&self, index: usize) -> bool {
        self[index / T::BITS].get_bit(index % T::BITS)
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

impl<T> FromBits for Vec<T>
where
    T: FromBits,
{
    fn from_lsb0(iter: impl IntoIterator<Item = bool>) -> Self {
        let mut iter = iter.into_iter().peekable();
        let mut vec = Vec::new();
        while iter.peek().is_some() {
            vec.push(T::from_lsb0(iter.by_ref()));
        }
        vec
    }

    fn from_msb0(iter: impl IntoIterator<Item = bool>) -> Self {
        let mut iter = iter.into_iter().peekable();
        let mut vec = Vec::new();
        while iter.peek().is_some() {
            vec.push(T::from_msb0(iter.by_ref()));
        }
        vec
    }
}
