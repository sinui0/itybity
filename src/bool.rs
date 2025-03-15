use crate::{BitIterable, BitLength, BitOrder, FromBitIterator, GetBit};

impl BitLength for bool {
    const BITS: usize = 1;
}

impl<O> GetBit<O> for bool
where
    O: BitOrder,
{
    fn get_bit(&self, index: usize) -> bool {
        assert!(index < 1, "index out of bounds");
        *self
    }
}

impl BitIterable for bool {}

impl FromBitIterator for bool {
    fn from_lsb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
        iter.into_iter().next().unwrap_or_default()
    }

    fn from_msb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
        iter.into_iter().next().unwrap_or_default()
    }
}
