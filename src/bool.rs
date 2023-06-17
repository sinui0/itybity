use crate::BitLength;

impl BitLength for bool {
    const BITS: usize = 1;
}

impl BitLength for &bool {
    const BITS: usize = 1;
}
