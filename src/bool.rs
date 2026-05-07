use crate::{BitIterable, BitLength, BitOrder, FromBitIterator, GetBit, SetBit};

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

impl<O> SetBit<O> for bool
where
    O: BitOrder,
{
    fn set_bit(&mut self, index: usize, value: bool) {
        assert!(index < 1, "index out of bounds");
        *self = value;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Lsb0, Msb0};

    #[test]
    fn set_bit_bool() {
        let mut b = false;
        SetBit::<Lsb0>::set_bit(&mut b, 0, true);
        assert!(b);
        SetBit::<Msb0>::set_bit(&mut b, 0, false);
        assert!(!b);
    }

    #[test]
    #[should_panic]
    fn set_bit_bool_out_of_bounds() {
        let mut b = false;
        SetBit::<Lsb0>::set_bit(&mut b, 1, true);
    }
}
