use crate::{BitIterable, BitLength, FromBitIterator, GetBit, Lsb0, Msb0};

macro_rules! impl_uint_from_bits {
    ($typ:ty) => {
        impl FromBitIterator for $typ {
            fn from_lsb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
                let mut iter = iter.into_iter();

                let mut value = <$typ>::default();
                for i in 0..<$typ>::BITS {
                    if let Some(bit) = iter.next() {
                        value |= (bit as $typ) << i;
                    } else {
                        return value;
                    }
                }

                value
            }

            fn from_msb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
                let mut iter = iter.into_iter();

                let mut value = <$typ>::default();
                for i in 0..<$typ>::BITS {
                    if let Some(bit) = iter.next() {
                        value |= (bit as $typ) << ((<$typ>::BITS - 1) - i);
                    } else {
                        return value;
                    }
                }

                value
            }
        }
    };
}

impl_uint_from_bits!(u8);
impl_uint_from_bits!(u16);
impl_uint_from_bits!(u32);
impl_uint_from_bits!(u64);
impl_uint_from_bits!(u128);
impl_uint_from_bits!(usize);

macro_rules! impl_get_bit_uint {
    ($ty:ty) => {
        impl BitLength for $ty {
            const BITS: usize = <$ty>::BITS as usize;
        }

        impl GetBit<Lsb0> for $ty {
            #[inline]
            fn get_bit(&self, index: usize) -> bool {
                assert!(index < <$ty>::BITS as usize);
                self & (1 << index) != 0
            }
        }

        impl GetBit<Msb0> for $ty {
            #[inline]
            fn get_bit(&self, index: usize) -> bool {
                const BIT_MASK: $ty = 1 << (<$ty>::BITS - 1);

                assert!(index < <$ty>::BITS as usize);
                self & (BIT_MASK >> index) != 0
            }
        }

        impl BitIterable for $ty {}
    };
}

impl_get_bit_uint!(u8);
impl_get_bit_uint!(u16);
impl_get_bit_uint!(u32);
impl_get_bit_uint!(u64);
impl_get_bit_uint!(u128);
impl_get_bit_uint!(usize);
