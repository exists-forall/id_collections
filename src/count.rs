//! The [`Count<I>`] structure and related types.

use num_traits::{CheckedAdd, CheckedSub, NumCast, One, ToPrimitive, Zero};
use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
    iter::{DoubleEndedIterator, FusedIterator},
    marker::PhantomData,
};

use crate::id::Id;

/// A range of strongly-typed indices, starting from zero.
///
/// The `Count<I>` type provides a strongly-typed way of representing the length of a range of id
/// values of type `I`, starting at zero. For example, the [`.count()`](crate::IdVec::count) method
/// on [`IdVec<I, T>`](crate::IdVec) returns a value of type `Count<I>`, representing the number of
/// elements in the collection:
///
/// ```
/// use id_collections::{Count, IdVec, id_type};
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct CityId(u32);
///
/// let mut cities: IdVec<CityId, &str> = IdVec::new();
/// let _ = cities.push("Toronto");
/// let _ = cities.push("Beijing");
/// let _ = cities.push("São Paulo");
/// let city_count: Count<CityId> = cities.count();
/// assert_eq!(city_count.to_value(), 3);
/// ```
///
/// Using a strongly-typed `Count<I>` value instead of a raw `usize` prevents us from mixing up size
/// values which refer to different types of ids:
///
/// ```compile_fail
/// # use id_collections::{Count, IdVec, id_type};
/// #
/// # #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// # struct CityId(u32);
/// #
/// # let mut cities: IdVec<CityId, &str> = IdVec::new();
/// # let _ = cities.push("Toronto");
/// # let _ = cities.push("Beijing");
/// # let _ = cities.push("São Paulo");
/// #
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct CountryId(u32);
///
/// // error: 'cities.count()' has type 'Count<CityId>', not 'Count<CountryId>'
/// let country_count: Count<CountryId> = cities.count();
/// ```
///
/// You can iterate over a `Count<I>` to obtain a sequence of ids. This makes it easy to iterate
/// over the ids of an [`IdVec<I, T>`](crate::IdVec):
///
/// ```
/// # use id_collections::{Count, IdVec, id_type};
/// #
/// # #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// # struct CityId(u32);
/// #
/// # let mut cities: IdVec<CityId, &str> = IdVec::new();
/// # let _ = cities.push("Toronto");
/// # let _ = cities.push("Beijing");
/// # let _ = cities.push("São Paulo");
/// #
/// let mut city_ids = Vec::new();
/// for city in cities.count() {
///     city_ids.push(city);
/// }
/// assert_eq!(city_ids, vec![CityId(0), CityId(1), CityId(2)]);
/// ```
///
/// You can also use a `Count<I>` as a counter to generate sequentially-assigned ids of type `I`,
/// via the [`Count::inc`] method:
///
/// ```
/// use id_collections::{Count, id_type};
/// use std::collections::HashMap;
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct WordId(u64);
///
/// let mut unique_words: HashMap<&str, WordId> = HashMap::new();
/// let mut word_count: Count<WordId> = Count::new();
///
/// let phrase = "the average of the reciprocal is not the reciprocal of the average";
/// for word in phrase.split(" ") {
///     unique_words.entry(word).or_insert_with(|| word_count.inc());
/// }
///
/// assert_eq!(
///     unique_words,
///     HashMap::from_iter([
///         ("the", WordId(0)), ("average", WordId(1)), ("of", WordId(2)),
///         ("reciprocal", WordId(3)), ("is", WordId(4)), ("not", WordId(5)),
///     ]),
/// );
/// ```
///
/// # Serde Support
///
/// When the `serde` Cargo feature is enabled, `Count<I>` can be serialized and deserialized using
/// [Serde](https://serde.rs/). A `Count<I>` is serialized exactly like its underlying integer
/// type [`I::Index`](crate::Id::Index).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct Count<I: Id> {
    value: I::Index,
}

impl<I: Id + Debug> Debug for Count<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_tuple("Count")
            .field(&I::from_index(self.value))
            .finish()
    }
}

impl<I: Id> Default for Count<I> {
    #[inline]
    fn default() -> Self {
        Count {
            value: I::Index::zero(),
        }
    }
}

impl<I: Id> Count<I> {
    /// Constructs a new, empty `Count<I>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let empty: Count<u32> = Count::new();
    /// assert_eq!(empty.to_value(), 0);
    /// assert!(empty.is_empty());
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns `true` if the range represented by the `Count<I>` contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::new();
    /// assert!(count.is_empty());
    /// ```
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::from_value(5);
    /// assert!(!count.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.value.is_zero()
    }

    /// Returns `true` if the range represented by the `Count<I>` contains `id`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::from_value(5);
    /// assert!(count.contains(0));
    /// assert!(count.contains(4));
    /// assert!(!count.contains(5));
    /// assert!(!count.contains(1000));
    /// ```
    #[inline]
    pub fn contains<J: Borrow<I>>(&self, id: J) -> bool {
        id.borrow().to_index() < self.value
    }

    /// Constructs a `Count<I>` with a given `value`.
    ///
    /// The returned `Count<I>` represents the id range `I::from_index(0), I::from_index(1), ...,
    /// I::from_index(value - 1)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::from_value(5);
    /// assert_eq!(count.to_value(), 5);
    /// let ids: Vec<u32> = count.into_iter().collect::<Vec<_>>();
    /// assert_eq!(ids, vec![0, 1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn from_value(value: I::Index) -> Self {
        Count { value }
    }

    /// Gets the number of ids in the range represented by the `Count<I>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::from_value(5);
    /// assert_eq!(count.to_value(), 5);
    /// ```
    #[inline]
    pub fn to_value(self) -> I::Index {
        self.value
    }

    /// Tries to construct a `Count<I>` representing the range whose last id is `id`.
    ///
    /// # Errors
    ///
    /// Fails if `id` is the largest value representable in `I::Index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Result<Count<u32>, _> = Count::try_from_last_id(5);
    /// assert!(count.is_ok());
    /// let count = count.unwrap();
    /// let ids = count.into_iter().collect::<Vec<_>>();
    /// assert_eq!(ids, vec![0, 1, 2, 3, 4, 5]);
    /// assert_eq!(count.to_value(), 6);
    /// ```
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Result<Count<u8>, _> = Count::try_from_last_id(255);
    /// assert!(count.is_err());
    /// ```
    #[inline]
    pub fn try_from_last_id(id: I) -> Result<Self, TryFromLastIdError<I>> {
        id.to_index()
            .checked_add(&I::Index::one())
            .map(Self::from_value)
            .ok_or_else(TryFromLastIdError::new)
    }

    /// Constructs a `Count<I>` representing the range whose last id is `id`.
    ///
    /// # Panics
    ///
    /// Panics if `id` is the largest value representable in `I::Index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::from_last_id(5);
    /// let ids = count.into_iter().collect::<Vec<_>>();
    /// assert_eq!(ids, vec![0, 1, 2, 3, 4, 5]);
    /// assert_eq!(count.to_value(), 6);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::Count;
    /// let count: Count<u8> = Count::from_last_id(255); // panics!
    /// ```
    #[inline]
    pub fn from_last_id(id: I) -> Self {
        match Self::try_from_last_id(id) {
            Ok(count) => count,
            Err(err) => panic!("{err}"),
        }
    }

    /// Gets the last id in the range of ids represented by the `Count<I>`, or `None` if the range
    /// is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::from_value(5);
    /// assert_eq!(count.last_id(), Some(4));
    /// ```
    ///
    /// ```
    /// # use id_collections::Count;
    /// let count: Count<u32> = Count::new();
    /// assert!(count.last_id().is_none());
    /// ```
    #[inline]
    pub fn last_id(&self) -> Option<I> {
        self.value.checked_sub(&I::Index::one()).map(I::from_index)
    }

    /// Tries to increment the `Count<I>`, returning the new largest id in the represented range.
    ///
    /// # Errors
    ///
    /// Fails if the new count overflows `I::Index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let mut count: Count<u32> = Count::from_value(5);
    /// let new_id = count.try_inc();
    /// assert!(new_id.is_ok());
    /// assert_eq!(new_id.unwrap(), 5);
    /// assert_eq!(count.to_value(), 6);
    /// ```
    ///
    /// ```
    /// # use id_collections::Count;
    /// let mut count: Count<u8> = Count::from_value(255);
    /// let result = count.try_inc();
    /// assert!(result.is_err());
    /// ```
    #[inline]
    pub fn try_inc(&mut self) -> Result<I, TryIncError<I>> {
        let new_value = self
            .value
            .checked_add(&I::Index::one())
            .ok_or_else(TryIncError::new)?;
        let result = I::from_index(self.value);
        self.value = new_value;
        Ok(result)
    }

    /// Increments the `Count<I>`, returning the new largest id in the represented range.
    ///
    /// # Panics
    ///
    /// Panics if the new count overflows `I::Index`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::Count;
    /// let mut count: Count<u32> = Count::from_value(5);
    /// let new_id = count.inc();
    /// assert_eq!(new_id, 5);
    /// assert_eq!(count.to_value(), 6);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::Count;
    /// let mut count: Count<u8> = Count::from_value(255);
    /// let result = count.inc(); // panics!
    /// ```
    #[must_use]
    #[inline]
    pub fn inc(&mut self) -> I {
        match self.try_inc() {
            Ok(result) => result,
            Err(err) => panic!("{err}"),
        }
    }
}

impl<I: Id> IntoIterator for Count<I> {
    type Item = I;
    type IntoIter = IdRangeIter<I>;
    fn into_iter(self) -> Self::IntoIter {
        IdRangeIter::from_indices(I::Index::zero(), self.value)
    }
}

/// An iterator over a range of id values.
///
/// It is rarely necessary to construct iterators of type `IdRangeIter` directly. The `IdRangeIter`
/// type is returned from functions like [`Count::into_iter()`](crate::Count::into_iter) and
/// [`IdVec::extend`](crate::IdVec::extend).
///
/// # Examples
///
/// ```
/// # use id_collections::{IdVec, count::IdRangeIter};
/// let mut v: IdVec<u32, &str> = IdVec::new();
/// let foo_id = v.push("foo");
/// let bar_id = v.push("bar");
/// let ids_iter: IdRangeIter<u32> = v.count().into_iter();
/// let ids = ids_iter.collect::<Vec<_>>();
/// assert_eq!(ids, vec![foo_id, bar_id]);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct IdRangeIter<I: Id> {
    // inclusive bound
    start: I::Index,
    // exclusive bound
    end: I::Index,
}

impl<I: Id> IdRangeIter<I> {
    /// Creates a new empty `IdRangeIter`.
    #[inline]
    pub fn empty() -> Self {
        IdRangeIter {
            start: I::Index::zero(),
            end: I::Index::zero(),
        }
    }

    #[inline]
    /// Creates a new `IdRangeIter` with a given `start` index (inclusive) and `end` index
    /// (exclusive).
    ///
    /// # Panics
    ///
    /// Panics if `start > end`.
    pub fn from_indices(start: I::Index, end: I::Index) -> Self {
        if start > end {
            panic!(
                "cannot construct IdRangeIter from indices: expected start <= end, found \
                 start = {start}, end = {end}"
            );
        }
        IdRangeIter { start, end }
    }

    /// Returns the start (inclusive) of the range represented by the `IdRangeIter`.
    ///
    /// Calling forward iterator methods like `next()` will increase this value.
    #[inline]
    pub fn start_index(&self) -> I::Index {
        self.start
    }

    /// Returns the end (exclusive) of the range represented by the `IdRangeIter`.
    ///
    /// Calling backward iterator methods like `next_back()` will decrease this value.
    #[inline]
    pub fn end_index(&self) -> I::Index {
        self.end
    }
}

impl<I: Id> Iterator for IdRangeIter<I> {
    type Item = I;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let next = self.start;
            self.start = self.start + I::Index::one();
            Some(I::from_index(next))
        } else {
            debug_assert!(self.start == self.end);
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.start < self.end {
            let hint = (self.end - self.start).to_usize();
            (hint.unwrap_or(usize::MAX), hint)
        } else {
            (0, Some(0))
        }
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(n_in_bounds) = <I::Index as NumCast>::from(n) {
            if let Some(plus_n) = self.start.checked_add(&n_in_bounds) {
                if plus_n < self.end {
                    self.start = plus_n + I::Index::one();
                    return Some(I::from_index(plus_n));
                }
            }
        }

        self.start = self.end;
        None
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    #[inline]
    fn min(mut self) -> Option<Self::Item> {
        self.next()
    }

    #[inline]
    fn max(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<I: Id> FusedIterator for IdRangeIter<I> {}

impl<I: Id> DoubleEndedIterator for IdRangeIter<I> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            self.end = self.end - I::Index::one();
            Some(I::from_index(self.end))
        } else {
            debug_assert!(self.start == self.end);
            None
        }
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if let Some(n_in_bounds) = <I::Index as NumCast>::from(n) {
            if let Some(minus_n) = self.end.checked_sub(&n_in_bounds) {
                if self.start < minus_n {
                    self.end = minus_n - I::Index::one();
                    return Some(I::from_index(self.end));
                }
            }
        }

        self.start = self.end;
        None
    }
}

impl<I: Id> ExactSizeIterator for IdRangeIter<I>
where
    I::Index: Into<usize>,
{
    #[inline]
    fn len(&self) -> usize {
        self.end.into() - self.start.into()
    }
}

#[cfg(test)]
mod iter_test {
    use crate::Count;

    #[test]
    fn test_size_hint() {
        assert_eq!(
            Count::<u32>::from_value(10).into_iter().size_hint(),
            (10, Some(10))
        );
    }

    #[test]
    fn test_nth() {
        let mut it = Count::<u32>::from_value(3).into_iter();
        assert_eq!(it.nth(1), Some(1));
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_last() {
        assert_eq!(Count::<u32>::from_value(10).into_iter().last(), Some(9));
    }

    #[test]
    fn test_min() {
        let mut it = Count::<u32>::from_value(4).into_iter();
        it.next();
        assert_eq!(it.min(), Some(1));
        assert_eq!(Count::<u32>::new().into_iter().min(), None);
    }

    #[test]
    fn test_max() {
        let mut it = Count::<u32>::from_value(4).into_iter();
        it.next_back();
        assert_eq!(it.max(), Some(2));
        assert_eq!(Count::<u32>::new().into_iter().max(), None);
    }

    #[test]
    fn test_next_back() {
        let mut it = Count::<u32>::from_value(3).into_iter();
        assert_eq!(it.next_back(), Some(2));
        assert_eq!(it.next_back(), Some(1));
        assert_eq!(it.next(), Some(0));
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
    }

    #[test]
    fn test_nth_back() {
        let mut it = Count::<u32>::from_value(4).into_iter();
        assert_eq!(it.nth_back(1), Some(2));
        assert_eq!(it.next_back(), Some(1));
        assert_eq!(it.next(), Some(0));
        assert_eq!(it.next(), None);
    }
}

/// An error indicating an integer overflow in [`Count::try_inc`].
#[derive(Clone, Debug)]
pub struct TryIncError<I: Id> {
    phantom: PhantomData<I>,
}

impl<I: Id> TryIncError<I> {
    fn new() -> Self {
        TryIncError {
            phantom: PhantomData,
        }
    }
}

impl<I: Id> Display for TryIncError<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot increment Count: value overflows range of {}",
            std::any::type_name::<I>()
        )
    }
}

impl<I: Id + Debug> std::error::Error for TryIncError<I> {}

/// An error indicating an integer overflow in [`Count::try_from_last_id`].
#[derive(Clone, Debug)]
pub struct TryFromLastIdError<I: Id> {
    phantom: PhantomData<I>,
}

impl<I: Id> TryFromLastIdError<I> {
    fn new() -> Self {
        TryFromLastIdError {
            phantom: PhantomData,
        }
    }
}

impl<I: Id> Display for TryFromLastIdError<I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot construct Count from last id: value overflows range of {}",
            std::any::type_name::<I>()
        )
    }
}

impl<I: Id + Debug> std::error::Error for TryFromLastIdError<I> {}
