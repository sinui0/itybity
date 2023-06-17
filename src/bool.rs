use crate::{BitLength, BitOrder, GetBit};

impl BitLength for bool {
    const BITS: usize = 1;
}

impl BitLength for &bool {
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

impl<O> GetBit<O> for &bool
where
    O: BitOrder,
{
    fn get_bit(&self, index: usize) -> bool {
        assert!(index < 1, "index out of bounds");
        **self
    }
}
