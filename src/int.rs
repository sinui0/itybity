use crate::{BitIterable, BitLength, FromBitIterator, GetBit, Lsb0, Msb0, SetBit};

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

        impl SetBit<Lsb0> for $ty {
            #[inline]
            fn set_bit(&mut self, index: usize, value: bool) {
                assert!(index < <$ty>::BITS as usize);
                let mask = (1 as $ty) << index;
                if value {
                    *self |= mask;
                } else {
                    *self &= !mask;
                }
            }
        }

        impl SetBit<Msb0> for $ty {
            #[inline]
            fn set_bit(&mut self, index: usize, value: bool) {
                assert!(index < <$ty>::BITS as usize);
                let mask = (1 as $ty) << ((<$ty>::BITS as usize - 1) - index);
                if value {
                    *self |= mask;
                } else {
                    *self &= !mask;
                }
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

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::*;

    macro_rules! set_bit_test {
        ($name:ident, $ty:ty) => {
            #[rstest]
            fn $name() {
                let bits = <$ty>::BITS as usize;

                for i in 0..bits {
                    let mut v: $ty = 0;
                    SetBit::<Lsb0>::set_bit(&mut v, i, true);
                    assert_eq!(v, (1 as $ty) << i);
                    assert!(GetBit::<Lsb0>::get_bit(&v, i));
                    SetBit::<Lsb0>::set_bit(&mut v, i, false);
                    assert_eq!(v, 0);

                    let mut v: $ty = 0;
                    SetBit::<Msb0>::set_bit(&mut v, i, true);
                    assert_eq!(v, (1 as $ty) << (bits - 1 - i));
                    assert!(GetBit::<Msb0>::get_bit(&v, i));
                    SetBit::<Msb0>::set_bit(&mut v, i, false);
                    assert_eq!(v, 0);
                }

                let mut v: $ty = !0;
                SetBit::<Lsb0>::set_bit(&mut v, 0, false);
                assert_eq!(v, !0 & !(1 as $ty));
                SetBit::<Lsb0>::set_bit(&mut v, 0, true);
                assert_eq!(v, !0);
            }
        };
    }

    set_bit_test!(set_bit_u8, u8);
    set_bit_test!(set_bit_u16, u16);
    set_bit_test!(set_bit_u32, u32);
    set_bit_test!(set_bit_u64, u64);
    set_bit_test!(set_bit_u128, u128);
    set_bit_test!(set_bit_usize, usize);
    set_bit_test!(set_bit_i8, i8);
    set_bit_test!(set_bit_i16, i16);
    set_bit_test!(set_bit_i32, i32);
    set_bit_test!(set_bit_i64, i64);
    set_bit_test!(set_bit_i128, i128);
    set_bit_test!(set_bit_isize, isize);

    #[test]
    #[should_panic]
    fn set_bit_lsb0_out_of_bounds() {
        let mut v: u8 = 0;
        SetBit::<Lsb0>::set_bit(&mut v, 8, true);
    }

    #[test]
    #[should_panic]
    fn set_bit_msb0_out_of_bounds() {
        let mut v: u8 = 0;
        SetBit::<Msb0>::set_bit(&mut v, 8, true);
    }
}
