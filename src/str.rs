#[cfg(feature = "alloc")]
extern crate alloc;

use crate::{FromBitIterator, StrToBits};

/// Iterator over a bit string.
///
/// This iterator will step over the _characters_ of a string,
/// yielding `true` for any character that is not `'0'`, and `false` otherwise.
#[derive(Debug, Clone)]
pub struct StrBitIter<'a> {
    chars: core::str::Chars<'a>,
}

impl<'a> StrToBits<'a> for str {
    fn iter_bits(&'a self) -> StrBitIter<'a> {
        StrBitIter::from(self)
    }
}

impl<'a> From<&'a str> for StrBitIter<'a> {
    fn from(str: &'a str) -> Self {
        StrBitIter { chars: str.chars() }
    }
}

impl<'a> Iterator for StrBitIter<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        self.chars.next().map(|c| c != '0')
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.chars.size_hint()
    }
}

impl<'a> DoubleEndedIterator for StrBitIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.chars.next_back().map(|c| c != '0')
    }
}

#[cfg(feature = "alloc")]
impl FromBitIterator for alloc::string::String {
    fn from_lsb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
        iter.into_iter()
            .map(|b| if b { '1' } else { '0' })
            .collect::<alloc::string::String>()
            .chars()
            .rev()
            .collect()
    }

    fn from_msb0_iter(iter: impl IntoIterator<Item = bool>) -> Self {
        iter.into_iter()
            .map(|b| if b { '1' } else { '0' })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::*;

    use crate::ToBits;

    #[rstest]
    #[case::empty_string("", vec![])]
    #[case::one_bit_1("1", vec![true])]
    #[case::one_bit_0("0", vec![false])]
    #[case::nibble("0101", vec![false, true, false, true])]
    #[case::non_binary_char("a", vec![true])]
    fn test_bit_string_iter(#[case] bits: &str, #[case] expected: Vec<bool>) {
        let bit_iter = bits.iter_bits();

        let bits: Vec<bool> = bit_iter.collect();

        assert_eq!(bits, expected);
    }

    #[rstest]
    #[case(0u8)]
    #[case(1u8)]
    #[case(2u8)]
    #[case(u8::MAX)]
    fn test_bit_string_from(#[case] value: u8) {
        let bits = value.to_msb0_vec();

        let expected_msb0 = format!("{:08b}", value);
        let expected_lsb0 = expected_msb0.chars().rev().collect::<String>();

        assert_eq!(String::from_msb0_iter(bits.clone()), expected_msb0);
        assert_eq!(String::from_lsb0_iter(bits), expected_lsb0);
    }
}
