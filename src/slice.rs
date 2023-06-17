use core::{iter::FusedIterator, marker::PhantomData};

use crate::{BitLength, BitOrder, GetBit, IntoBits, Lsb0, Msb0, ToBits};

/// Iterator over the bits of a slice.
pub struct SliceBitIter<'a, T, O>
where
    O: BitOrder,
{
    slice: &'a [T],
    pos: usize,
    len: usize,
    bit_order: PhantomData<O>,
}

impl<'a, T, O> From<&'a [T]> for SliceBitIter<'a, T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn from(slice: &'a [T]) -> Self {
        Self {
            slice,
            pos: 0,
            len: slice.len() * T::BITS,
            bit_order: PhantomData,
        }
    }
}

impl<'a, T, O> Iterator for SliceBitIter<'a, T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        if self.pos < self.len {
            let elem_idx = self.pos / T::BITS;
            let bit_idx = self.pos % T::BITS;

            let bit = self.slice[elem_idx].get_bit(bit_idx);
            self.pos += 1;
            Some(bit)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len - self.pos;
        (remaining, Some(remaining))
    }
}

impl<'a, T, O> ExactSizeIterator for SliceBitIter<'a, T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<'a, T, O> FusedIterator for SliceBitIter<'a, T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
}

impl<'a, T> ToBits<'a> for [T]
where
    T: GetBit<Lsb0> + GetBit<Msb0> + BitLength + 'a,
{
    type IterLsb0 = SliceBitIter<'a, T, Lsb0>;
    type IterMsb0 = SliceBitIter<'a, T, Msb0>;

    fn iter_lsb0(&'a self) -> Self::IterLsb0 {
        SliceBitIter::from(self)
    }

    fn iter_msb0(&'a self) -> Self::IterMsb0 {
        SliceBitIter::from(self)
    }
}

impl<'a, T> IntoBits for &'a [T]
where
    T: GetBit<Lsb0> + GetBit<Msb0> + BitLength + 'a,
{
    type IterLsb0 = SliceBitIter<'a, T, Lsb0>;
    type IterMsb0 = SliceBitIter<'a, T, Msb0>;

    fn into_iter_lsb0(self) -> Self::IterLsb0 {
        SliceBitIter::from(self)
    }

    fn into_iter_msb0(self) -> Self::IterMsb0 {
        SliceBitIter::from(self)
    }
}
