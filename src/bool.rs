use crate::{BitLength, IntoBits, ToBits};

impl BitLength for bool {
    const BITS: usize = 1;
}

impl BitLength for &bool {
    const BITS: usize = 1;
}

impl<'a> ToBits<'a> for bool {
    type IterLsb0 = core::iter::Once<bool>;
    type IterMsb0 = core::iter::Once<bool>;

    fn iter_lsb0(&'a self) -> Self::IterLsb0 {
        core::iter::once(*self)
    }

    fn iter_msb0(&'a self) -> Self::IterMsb0 {
        core::iter::once(*self)
    }
}

impl<'a, const N: usize> ToBits<'a> for [bool; N] {
    type IterLsb0 = core::iter::Copied<core::slice::Iter<'a, bool>>;
    type IterMsb0 = core::iter::Copied<core::slice::Iter<'a, bool>>;

    fn iter_lsb0(&'a self) -> Self::IterLsb0 {
        self.iter().copied()
    }

    fn iter_msb0(&'a self) -> Self::IterMsb0 {
        self.iter().copied()
    }
}

impl IntoBits for bool {
    type IterLsb0 = core::iter::Once<bool>;
    type IterMsb0 = core::iter::Once<bool>;

    fn into_iter_lsb0(self) -> Self::IterLsb0 {
        core::iter::once(self)
    }

    fn into_iter_msb0(self) -> Self::IterMsb0 {
        core::iter::once(self)
    }
}
