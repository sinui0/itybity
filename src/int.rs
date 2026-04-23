use crate::{BitIterable, BitLength, FromBitIterator, GetBit, Lsb0, Msb0};

macro_rules! impl_int_from_bits {
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

impl_int_from_bits!(u8);
impl_int_from_bits!(u16);
impl_int_from_bits!(u32);
impl_int_from_bits!(u64);
impl_int_from_bits!(u128);
impl_int_from_bits!(usize);
impl_int_from_bits!(i8);
impl_int_from_bits!(i16);
impl_int_from_bits!(i32);
impl_int_from_bits!(i64);
impl_int_from_bits!(i128);
impl_int_from_bits!(isize);

macro_rules! impl_get_bit_int {
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
                assert!(index < <$ty>::BITS as usize);
                self & (1 << ((<$ty>::BITS as usize - 1) - index)) != 0
            }
        }

        impl BitIterable for $ty {}
    };
}

impl_get_bit_int!(u8);
impl_get_bit_int!(u16);
impl_get_bit_int!(u32);
impl_get_bit_int!(u64);
impl_get_bit_int!(u128);
impl_get_bit_int!(usize);
impl_get_bit_int!(i8);
impl_get_bit_int!(i16);
impl_get_bit_int!(i32);
impl_get_bit_int!(i64);
impl_get_bit_int!(i128);
impl_get_bit_int!(isize);
