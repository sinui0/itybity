use crate::BitLength;

impl BitLength for bool {
    const BITS: usize = 1;
}

impl<const N: usize> BitLength for [bool; N] {
    const BITS: usize = N;
}

impl<const N: usize> BitLength for &[bool; N] {
    const BITS: usize = N;
}

impl BitLength for &bool {
    const BITS: usize = 1;
}

impl<const N: usize> BitLength for [&bool; N] {
    const BITS: usize = N;
}

impl<const N: usize> BitLength for &[&bool; N] {
    const BITS: usize = N;
}
