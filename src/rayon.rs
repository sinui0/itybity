use core::{fmt::Debug, marker::PhantomData, ops::Range};

use rayon::{
    iter::{
        plumbing::{bridge, Consumer, Producer, ProducerCallback, UnindexedConsumer},
        FlatMap, ParallelIterator,
    },
    prelude::{IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator},
};

use crate::{BitIter, BitIterable, BitLength, BitOrder, GetBit, Lsb0, Msb0};

/// Trait for types that can be converted into a borrowing parallel bit iterator.
///
/// # Note
///
/// This trait should be preferred over [`IntoParallelBits`] as it allows
/// shared access to the underlying data without cloning.
pub trait ToParallelBits<'a> {
    /// The Lsb0 parallel bit iterator type.
    type IterLsb0: ParallelIterator<Item = bool>;
    /// The Msb0 parallel bit iterator type.
    type IterMsb0: ParallelIterator<Item = bool>;

    /// Creates a parallel bit iterator over `self` in Lsb0 order.
    fn par_iter_lsb0(&'a self) -> Self::IterLsb0;

    /// Creates a parallel bit iterator over `self` in Msb0 order.
    fn par_iter_msb0(&'a self) -> Self::IterMsb0;
}

impl<'a, T> ToParallelBits<'a> for T
where
    T: BitIterable + Sync + 'a,
{
    type IterLsb0 = ParallelBitIterRef<'a, T, Lsb0>;
    type IterMsb0 = ParallelBitIterRef<'a, T, Msb0>;

    fn par_iter_lsb0(&'a self) -> Self::IterLsb0 {
        ParallelBitIterRef::from(self)
    }

    fn par_iter_msb0(&'a self) -> Self::IterMsb0 {
        ParallelBitIterRef::from(self)
    }
}

/// Trait for types that can be converted into a parallel bit iterator.
///
/// # Note
///
/// [`ToParallelBits`] should be preferred over [`IntoParallelBits`] as it allows
/// shared access to the underlying data without cloning.
pub trait IntoParallelBits
where
    Self: BitIterable + Send,
{
    /// The Lsb0 parallel bit iterator type.
    type IterLsb0: ParallelIterator<Item = bool>;
    /// The Msb0 parallel bit iterator type.
    type IterMsb0: ParallelIterator<Item = bool>;

    /// Converts `self` into a parallel bit iterator in Lsb0 order.
    fn into_par_iter_lsb0(self) -> Self::IterLsb0;

    /// Converts `self` into a parallel bit iterator in Msb0 order.
    fn into_par_iter_msb0(self) -> Self::IterMsb0;
}

impl<T> IntoParallelBits for T
where
    T: BitIterable + Clone + Send,
{
    type IterLsb0 = ParallelBitIter<T, Lsb0>;
    type IterMsb0 = ParallelBitIter<T, Msb0>;

    fn into_par_iter_lsb0(self) -> Self::IterLsb0 {
        ParallelBitIter::from(self)
    }

    fn into_par_iter_msb0(self) -> Self::IterMsb0 {
        ParallelBitIter::from(self)
    }
}

/// Trait for converting parallel iterators over values into parallel iterators over bits.
///
/// This trait is automatically implemented for all types that implement [`IntoParallelIterator`] where
/// the item type implements [`IntoParallelBits`].
///
/// # Note
///
/// This trait uses [`IntoParallelBits`] to convert the underlying type into a bit iterator. This causes
/// the underlying type to be cloned for each iterator.
///
/// See [`IntoParallelRefBitIterator`] for a trait which allows iterating over the bits of the underlying data
/// without cloning.
pub trait IntoParallelBitIterator {
    /// The Lsb0 parallel bit iterator type.
    type IterLsb0: ParallelIterator<Item = bool>;
    /// The Msb0 parallel bit iterator type.
    type IterMsb0: ParallelIterator<Item = bool>;

    /// Converts `self` into a parallel bit iterator in Lsb0 order.
    fn into_par_iter_lsb0(self) -> Self::IterLsb0;

    /// Converts `self` into a parallel bit iterator in Msb0 order.
    fn into_par_iter_msb0(self) -> Self::IterMsb0;
}

impl<T> IntoParallelBitIterator for T
where
    T: IntoParallelIterator,
    T::Item: IntoParallelBits,
{
    type IterLsb0 = FlatMap<T::Iter, fn(T::Item) -> <T::Item as IntoParallelBits>::IterLsb0>;
    type IterMsb0 = FlatMap<T::Iter, fn(T::Item) -> <T::Item as IntoParallelBits>::IterMsb0>;

    fn into_par_iter_lsb0(self) -> Self::IterLsb0 {
        self.into_par_iter()
            .flat_map(IntoParallelBits::into_par_iter_lsb0)
    }

    fn into_par_iter_msb0(self) -> Self::IterMsb0 {
        self.into_par_iter()
            .flat_map(IntoParallelBits::into_par_iter_msb0)
    }
}

/// Trait for converting parallel iterators over value *references* into parallel iterators over bits.
///
/// This trait is automatically implemented for all types that implement [`IntoParallelRefIterator`] where
/// the item type implements [`ToParallelBits`].
///
/// Use of this trait is preferred instead of [`IntoParallelBitIterator`] as it allows shared access to
/// the underlying data without cloning.
pub trait IntoParallelRefBitIterator<'a> {
    /// The Lsb0 parallel bit iterator type.
    type IterLsb0: ParallelIterator<Item = bool> + 'a;
    /// The Msb0 parallel bit iterator type.
    type IterMsb0: ParallelIterator<Item = bool> + 'a;

    /// Creates a parallel bit iterator over `self` in Lsb0 order.
    fn par_iter_lsb0(&'a self) -> Self::IterLsb0;

    /// Creates a parallel bit iterator over `self` in Msb0 order.
    fn par_iter_msb0(&'a self) -> Self::IterMsb0;
}

impl<'a, T> IntoParallelRefBitIterator<'a> for T
where
    T: IntoParallelRefIterator<'a> + ?Sized,
    T::Iter: 'a,
    T::Item: BitIterable + Sync + Clone + 'a,
{
    type IterLsb0 = FlatMap<T::Iter, fn(T::Item) -> <T::Item as IntoParallelBits>::IterLsb0>;
    type IterMsb0 = FlatMap<T::Iter, fn(T::Item) -> <T::Item as IntoParallelBits>::IterMsb0>;

    fn par_iter_lsb0(&'a self) -> Self::IterLsb0 {
        self.par_iter()
            .flat_map(IntoParallelBits::into_par_iter_lsb0)
    }

    fn par_iter_msb0(&'a self) -> Self::IterMsb0 {
        self.par_iter()
            .flat_map(IntoParallelBits::into_par_iter_msb0)
    }
}

/// Parallel iterator over bits.
#[derive(Debug, Clone)]
pub struct ParallelBitIter<T, O>
where
    O: BitOrder,
{
    range: Range<usize>,
    bit_order: PhantomData<O>,
    value: T,
}

impl<T, O> From<T> for ParallelBitIter<T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn from(value: T) -> Self {
        Self {
            value,
            range: 0..T::BITS,
            bit_order: PhantomData,
        }
    }
}

impl<T, O> ParallelIterator for ParallelBitIter<T, O>
where
    T: GetBit<O> + BitLength + Clone + Send,
    O: BitOrder,
{
    type Item = bool;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.range.len())
    }
}

impl<T, O> IndexedParallelIterator for ParallelBitIter<T, O>
where
    T: GetBit<O> + BitLength + Clone + Send,
    O: BitOrder,
{
    fn len(&self) -> usize {
        self.range.len()
    }

    fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
        bridge(self, consumer)
    }

    fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
        callback.callback(self)
    }
}

impl<T, O> Producer for ParallelBitIter<T, O>
where
    T: GetBit<O> + BitLength + Clone + Send,
    O: BitOrder,
{
    type Item = bool;
    type IntoIter = BitIter<T, O>;

    fn into_iter(self) -> Self::IntoIter {
        BitIter {
            value: self.value,
            range: self.range,
            bit_order: PhantomData,
        }
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        assert!(index <= self.range.len());

        let mid = self.range.start.wrapping_add(index);
        let left = self.range.start..mid;
        let right = mid..self.range.end;

        (
            Self {
                value: self.value.clone(),
                range: left,
                bit_order: PhantomData,
            },
            Self {
                value: self.value,
                range: right,
                bit_order: PhantomData,
            },
        )
    }
}

/// Parallel iterator over bits by reference.
#[derive(Debug, Clone)]
pub struct ParallelBitIterRef<'a, T, O>
where
    O: BitOrder,
{
    range: Range<usize>,
    bit_order: PhantomData<O>,
    value: &'a T,
}

impl<'a, T, O> From<&'a T> for ParallelBitIterRef<'a, T, O>
where
    T: GetBit<O> + BitLength,
    O: BitOrder,
{
    fn from(value: &'a T) -> Self {
        Self {
            value,
            range: 0..T::BITS,
            bit_order: PhantomData,
        }
    }
}

impl<'a, T, O> ParallelIterator for ParallelBitIterRef<'a, T, O>
where
    T: GetBit<O> + BitLength + Sync,
    O: BitOrder,
{
    type Item = bool;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        bridge(self, consumer)
    }

    fn opt_len(&self) -> Option<usize> {
        Some(self.range.len())
    }
}

impl<'a, T, O> IndexedParallelIterator for ParallelBitIterRef<'a, T, O>
where
    T: GetBit<O> + BitLength + Sync,
    O: BitOrder,
{
    fn len(&self) -> usize {
        self.range.len()
    }

    fn drive<C: Consumer<Self::Item>>(self, consumer: C) -> C::Result {
        bridge(self, consumer)
    }

    fn with_producer<CB: ProducerCallback<Self::Item>>(self, callback: CB) -> CB::Output {
        callback.callback(self)
    }
}

impl<'a, T, O> Producer for ParallelBitIterRef<'a, T, O>
where
    T: GetBit<O> + BitLength + Sync,
    O: BitOrder,
{
    type Item = bool;
    type IntoIter = BitIter<&'a T, O>;

    fn into_iter(self) -> Self::IntoIter {
        BitIter {
            value: self.value,
            range: self.range,
            bit_order: PhantomData,
        }
    }

    fn split_at(self, index: usize) -> (Self, Self) {
        assert!(index <= self.range.len());

        let mid = self.range.start.wrapping_add(index);
        let left = self.range.start..mid;
        let right = mid..self.range.end;

        (
            Self {
                value: self.value,
                range: left,
                bit_order: PhantomData,
            },
            Self {
                value: self.value,
                range: right,
                bit_order: PhantomData,
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::*;

    use crate::StrToBits;

    trait Fixtures<T> {
        const ZERO: T;
        const ONE: T;
        const TWO: T;
        const MAX: T;
    }

    macro_rules! impl_fixtures {
        ($($ty:ty),*) => {
            $(
                impl Fixtures<$ty> for $ty {
                    const ZERO: $ty = 0;
                    const ONE: $ty = 1;
                    const TWO: $ty = 2;
                    const MAX: $ty = <$ty>::MAX;
                }
            )*
        };
    }

    impl_fixtures!(u8, u16, u32, u64, u128, usize);

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_into_par_bit_iter<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T> + BitIterable + Clone + Send + Copy + std::fmt::Binary,
    {
        for value in [T::ZERO, T::ONE, T::TWO, T::MAX] {
            let expected_msb0_bits = format!("{:0width$b}", value, width = T::BITS).to_bit_vec();
            let expected_lsb0_bits = expected_msb0_bits
                .iter()
                .copied()
                .rev()
                .collect::<Vec<bool>>();

            assert_eq!(
                value.into_par_iter_msb0().collect::<Vec<bool>>(),
                expected_msb0_bits
            );
            assert_eq!(
                value.into_par_iter_lsb0().collect::<Vec<bool>>(),
                expected_lsb0_bits
            );
        }
    }

    #[rstest]
    #[case::u8(PhantomData::<u8>)]
    #[case::u16(PhantomData::<u16>)]
    #[case::u32(PhantomData::<u32>)]
    #[case::u64(PhantomData::<u64>)]
    #[case::u128(PhantomData::<u128>)]
    #[case::usize(PhantomData::<usize>)]
    fn test_to_par_bit_iter_slice<T>(#[case] _ty: PhantomData<T>)
    where
        T: Fixtures<T> + BitIterable + Copy + Sync + std::fmt::Binary,
    {
        let expected_msb0_bits = format!(
            "{:0width$b}{:0width$b}{:0width$b}{:0width$b}",
            T::ZERO,
            T::ONE,
            T::TWO,
            T::MAX,
            width = T::BITS
        )
        .to_bit_vec();
        let expected_lsb0_bits = expected_msb0_bits
            .chunks(T::BITS)
            .flat_map(|chunk| chunk.iter().copied().rev())
            .collect::<Vec<bool>>();

        let slice = [T::ZERO, T::ONE, T::TWO, T::MAX];

        assert_eq!(
            slice.par_iter_msb0().collect::<Vec<bool>>(),
            expected_msb0_bits
        );
        assert_eq!(
            slice.par_iter_lsb0().collect::<Vec<bool>>(),
            expected_lsb0_bits
        );
    }
}
