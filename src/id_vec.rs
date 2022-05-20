//! The [`IdVec<I, T>`] structure and related types.

use num_traits::{CheckedAdd, NumCast, One, ToPrimitive, Zero};
use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::TryReserveError,
    fmt::{Debug, Display},
    iter::FusedIterator,
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use crate::{
    count::{Count, IdRangeIter},
    id::{FromPrimIntUnchecked, Id},
};

/// A vector-like data structure with strongly-typed indices.
///
/// An `IdVec<I, T>` is like a [`Vec<T>`] which uses a custom index type `I` for its indices instead
/// of [`usize`]. The custom index type of an `IdVec<I, T>` is called its "id type." You can define
/// your own id types and use them with `IdVec`:
///
/// ```
/// use id_collections::{IdVec, id_type};
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct CityId(u32);
///
/// let mut cities: IdVec<CityId, &str> = IdVec::new();
///
/// // the 'push' method returns the id of the newly-inserted element:
/// let toronto_id: CityId = cities.push("Toronto");
/// let beijing_id: CityId = cities.push("Beijing");
/// let são_paulo_id: CityId = cities.push("São Paulo");
///
/// // you can index an 'IdVec' using its id type:
/// assert_eq!(cities[toronto_id], "Toronto");
/// assert_eq!(cities[beijing_id], "Beijing");
/// assert_eq!(cities[são_paulo_id], "São Paulo");
/// ```
///
/// Using `IdVec<I, T>` instead of `Vec<T>` helps avoid logic errors resulting from mixing up id
/// types. If you try to index into an `IdVec<I, T>` using a raw [`usize`], or a different id type,
/// you'll get a type error at compile time:
///
/// ```compile_fail
/// # use id_collections::{IdVec, id_type};
/// #
/// # #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// # struct CityId(u32);
/// #
/// # let cities: IdVec<CityId, &str> = IdVec::new();
/// #
/// // error: cannot index 'IdVec<CityId, &str>' using index of type 'usize'
/// let city_name = cities[2];
/// ```
///
/// ```compile_fail
/// # use id_collections::{IdVec, id_type};
/// #
/// # #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// # struct CityId(u32);
/// #
/// # let cities: IdVec<CityId, &str> = IdVec::new();
/// #
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct CountryId(u32);
///
/// // error: cannot index 'IdVec<CityId, &str>' using index of type 'CountryId'
/// let city_name = cities[CountryId(2)];
/// ```
///
/// Behind the scenes, `IdVec<I, T>` is just a wrapper around [`Vec<T>`]. You can cheaply convert
/// between [`Vec<T>`] and `IdVec<I, T>` using the functions [`IdVec::from_vec`] and
/// [`IdVec::into_vec`].
///
/// # Operations
///
/// - **Creating a new `IdVec<I, T>`**:
///     - [`IdVec::new`]
///     - [`IdVec::with_capacity`]
///     - [`IdVec::from_count_with`]
///     - [`IdVec::try_from_count_with`]
/// - **Accessing the size of an `IdVec<I, T>`**:
///     - [`IdVec::count`]
///     - [`IdVec::len`]
///     - [`IdVec::is_empty`]
/// - **Adding elements to an `IdVec<I, T>`**:
///     - [`IdVec::try_push`]
///     - [`IdVec::push`]
///     - [`IdVec::try_extend`]
///     - [`IdVec::extend`]
///     - [`IdVec::try_extend_from_slice`]
///     - [`IdVec::extend_from_slice`]
///     - [`IdVec::try_append`]
///     - [`IdVec::append`]
///     - [`IdVec::resize`]
///     - [`IdVec::resize_with`]
/// - **Removing elements from an `IdVec<I, T>`**:
///     - [`IdVec::pop`]
///     - [`IdVec::clear`]
///     - [`IdVec::truncate`]
///     - [`IdVec::drain_from`]
///     - [`IdVec::drain_all`]
/// - **Accessing elements of an `IdVec<I, T>`**:
///     - [`IdVec::get`]
///     - [`IdVec::index`] (the `arr[i]` operator)
///     - [`IdVec::get_mut`]
///     - [`IdVec::index_mut`] (the `arr[i]` operator)
///     - [`IdVec::get_pair_mut`]
///     - [`IdVec::swap`]
/// - **Transforming an `IdVec<I, T>`**:
///     - [`IdVec::map`]
///     - [`IdVec::map_refs`]
///     - [`IdVec::try_map`]
///     - [`IdVec::try_map_refs`]
/// - **Iterating over an `IdVec<I, T>`**:
///     - [`IdVec::count`] (using [`Count::into_iter`])
///     - [`IdVec::iter`]
///     - [`IdVec::iter_mut`]
///     - [`IdVec::into_iter`](struct.IdVec.html#impl-IntoIterator-2)
///     - [`IdVec::values`]
///     - [`IdVec::values_mut`]
///     - [`IdVec::into_values`]
/// - **Managing allocations**:
///     - [`IdVec::capacity`]
///     - [`IdVec::try_reserve`]
///     - [`IdVec::reserve`]
///     - [`IdVec::try_reserve_exact`]
///     - [`IdVec::reserve_exact`]
///     - [`IdVec::shrink_to_fit`]
///     - [`IdVec::shrink_to`]
/// - **Working with the underlying storage**:
///     - [`IdVec::try_from_vec`]
///     - [`IdVec::from_vec`]
///     - [`IdVec::into_vec`]
///     - [`IdVec::as_slice`]
///     - [`IdVec::as_mut_slice`]
///
/// # Serde Support
///
/// When the `serde` Cargo feature is enabled, `IdVec<I, T>` can be serialized and deserialized
/// using [Serde](https://serde.rs/). An `IdVec<I, T>` is serialized exactly like a [`Vec<T>`].
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct IdVec<I: Id, T> {
    #[cfg_attr(feature = "serde", serde(skip))]
    phantom: PhantomData<I>,
    #[cfg_attr(
        feature = "serde",
        serde(deserialize_with = "de_vec_bounds_checked::<I, _, _>")
    )]
    #[cfg_attr(
        feature = "serde",
        serde(bound(deserialize = "T: serde::de::Deserialize<'de>"))
    )]
    inner: Vec<T>,
}

#[cfg(feature = "serde")]
fn de_vec_bounds_checked<'de, I: Id, T: serde::de::Deserialize<'de>, D>(
    deserializer: D,
) -> Result<Vec<T>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de::{Deserialize, Error};
    let v = Vec::deserialize(deserializer)?;
    if <I::Index as NumCast>::from(v.len()).is_none() {
        return Err(D::Error::custom(format!(
            "sequence length exceeds bounds of index type {}",
            std::any::type_name::<I>()
        )));
    }
    Ok(v)
}

#[cfg(all(test, feature = "serde"))]
mod serde_test {
    use crate::{id_type, IdVec};

    #[test]
    fn test_serialize() {
        #[id_type]
        struct TestId(u32);

        let mut v: IdVec<TestId, &str> = IdVec::new();
        let _ = v.push("foo");
        let _ = v.push("bar");
        let serialized = serde_json::to_string(&v).unwrap();
        assert_eq!(&serialized, r#"["foo","bar"]"#)
    }

    #[test]
    fn test_deserialize() {
        #[id_type]
        struct TestId(u32);

        let serialized = r#"["foo","bar"]"#;
        let v: IdVec<TestId, String> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(v.as_slice(), &["foo".to_owned(), "bar".to_owned()]);
    }

    #[test]
    fn test_deserialize_out_of_bounds() {
        #[id_type]
        struct TestId(u8);

        let serialized = serde_json::to_string(&vec!["filler"; 256]).unwrap();
        assert!(serde_json::from_str::<IdVec<TestId, String>>(&serialized).is_err());
    }
}

impl<I: Id, T> Default for IdVec<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Id, T> IdVec<I, T> {
    /// Constructs a new, empty `IdVec<I, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v: IdVec<u32, i32> = IdVec::new();
    /// assert!(v.is_empty());
    /// ```
    pub fn new() -> Self {
        IdVec {
            phantom: PhantomData,
            inner: Vec::new(),
        }
    }

    /// Constructs a new, empty `IdVec<I, T>` with the specified capacity.
    ///
    /// This is a wrapper around `Vec::with_capacity`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v: IdVec<u32, i32> = IdVec::with_capacity(4);
    /// assert_eq!(v.capacity(), 4);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        IdVec {
            phantom: PhantomData,
            inner: Vec::with_capacity(capacity),
        }
    }

    /// Creates an `IdVec<I, T>` with `count` elements, generating each element using the provided
    /// function `f`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::{IdVec, Count};
    /// let v: IdVec<u32, u32> = IdVec::from_count_with(Count::from_value(5), |i| i * i);
    /// assert_eq!(v.as_slice(), &[0, 1, 4, 9, 16]);
    /// ```
    pub fn from_count_with<F>(count: Count<I>, mut f: F) -> IdVec<I, T>
    where
        F: FnMut(I) -> T,
    {
        match count.to_value().to_usize() {
            Some(count_usize) => Self::from_vec(
                (0..count_usize)
                    .map(|i| f(I::from_index(I::Index::from_usize_unchecked(i))))
                    .collect(),
            ),
            None => panic!("cannot create IdVec via from_count_with: id count overflows usize"),
        }
    }

    /// Tries to create an `IdVec<I, T>` with `count` elements, generating each element using the
    /// provided fallible function `f`.
    ///
    /// # Errors
    ///
    /// Returns the first error from `f`, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let strings: IdVec<u32, &str> = IdVec::from_vec(vec!["10", "20", "30"]);
    /// let numbers = IdVec::try_from_count_with(strings.count(), |i| strings[i].parse::<i32>());
    /// assert!(numbers.is_ok());
    /// assert_eq!(numbers.unwrap().as_slice(), &[10, 20, 30]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let strings: IdVec<u32, &str> = IdVec::from_vec(vec!["10", "20", "banana"]);
    /// let numbers = IdVec::try_from_count_with(strings.count(), |i| strings[i].parse::<i32>());
    /// assert!(numbers.is_err());
    /// ```
    pub fn try_from_count_with<F, E>(count: Count<I>, mut f: F) -> Result<IdVec<I, T>, E>
    where
        F: FnMut(I) -> Result<T, E>,
    {
        match count.to_value().to_usize() {
            Some(count_usize) => Ok(Self::from_vec(
                (0..count_usize)
                    .map(|i| f(I::from_index(I::Index::from_usize_unchecked(i))))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            None => panic!("cannot create IdVec via try_from_count_with: id count overflows usize"),
        }
    }

    /// Returns the size of the `IdVec<I, T>` as a [`Count<I>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::{IdVec, Count};
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// assert_eq!(v.count(), Count::from_value(2));
    /// ```
    #[doc(alias = "length")]
    #[doc(alias = "len")]
    #[doc(alias = "size")]
    #[doc(alias = "keys")]
    pub fn count(&self) -> Count<I> {
        Count::from_value(I::Index::from_usize_unchecked(self.len()))
    }

    /// Returns the length of the `IdVec<I, T>`.
    ///
    /// # See Also
    ///
    /// The [`.count()`][IdVec::count] method provides an altnerative to `.len()` which returns the
    /// size of the `IdVec<I, T>` as a strongly-typed [`Count<I>`] value instead of as a raw
    /// [`usize`]. It is often preferable to use [`.count()`](IdVec::count) over `.len()`, as the
    /// returned [`Count<I>`] value provides better type safety, and is compatible with other
    /// operations in this crate, like [`Count::into_iter`] and [`IdVec::from_count_with`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// assert_eq!(v.len(), 0);
    ///
    /// let _ = v.push("foo");
    /// assert_eq!(v.len(), 1);
    ///
    /// let _ = v.push("bar");
    /// assert_eq!(v.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the `IdVec<I, T>` contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// assert!(v.is_empty());
    ///
    /// v.push("foo");
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Tries to push an element onto the end of the `IdVec<I, T>`, returning the id of the new
    /// element.
    ///
    /// # Errors
    ///
    /// If the `IdVec<I, T>` does not have space to fit another element, returns an error containing
    /// the original `T` value unchanged. This can happen either because the length of the `IdVec<I,
    /// T>` cannot grow any larger without exceeding the largest representable value of `I`, or
    /// because of an allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.try_push("foo");
    /// assert_eq!(foo_id.unwrap(), 0);
    /// let bar_id = v.try_push("bar");
    /// assert_eq!(bar_id.unwrap(), 1);
    /// assert_eq!(v.as_slice(), &["foo", "bar"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..255 {
    ///     let result = v.try_push("filler");
    ///     assert!(result.is_ok());
    /// }
    /// // 'v' now has 255 elements, which is the largest value of 'u8'; we can't add any more!
    /// let result = v.try_push("foo");
    /// assert!(result.is_err());
    /// // we can use 'into_value' to extract the original value passed to 'try_push':
    /// assert!(result.unwrap_err().into_value() == "foo");
    /// ```
    pub fn try_push(&mut self, value: T) -> Result<I, TryPushError<I, T>> {
        let new_index = I::Index::from_usize_unchecked(self.inner.len());
        if new_index.checked_add(&I::Index::one()).is_some() && self.inner.try_reserve(1).is_ok() {
            self.inner.push(value);
            return Ok(I::from_index(new_index));
        }

        Err(TryPushError::new(value))
    }

    /// Pushes an element onto the end of the `IdVec<I, T>`, returning the id of the new element.
    ///
    /// # Panics
    ///
    /// Panics if the `IdVec<I, T>` does not have space to fit another element. This can happen
    /// either because the length of the `IdVec<I, T>` cannot grow any larger without exceeding the
    /// largest representable value of `I`, or because of an allocation failure in the underlying
    /// `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let bar_id = v.push("bar");
    /// assert_eq!(bar_id, 1);
    /// assert_eq!(v.as_slice(), &["foo", "bar"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..255 {
    ///     let _ = v.push("filler");
    /// }
    /// // 'v' now has 255 elements, which is the largest value of 'u8'; we can't add any more!
    /// let result = v.push("foo"); // panics!
    /// ```
    #[must_use]
    pub fn push(&mut self, value: T) -> I {
        match self.try_push(value) {
            Ok(id) => id,
            Err(err) => panic!("{err}"),
        }
    }

    /// Tries to push all elements of an iterator onto the end of an `IdVec<I, T>`. Returns an
    /// iterator over the ids of all newly-inserted elements.
    ///
    /// # Errors
    ///
    /// If the `IdVec<I, T>` does not have space to fit all the elements of `iter`, returns an
    /// error. This error condition can happen either because the length of the `IdVec<I, T>` cannot
    /// grow large enough to accomodate the new elements from `iter` without exceeding the largest
    /// representable value of `I`, or because of an allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let result = v.try_extend(vec!["bar", "baz"]);
    /// assert!(result.is_ok());
    /// let new_ids_iter = result.unwrap();
    /// let new_ids = new_ids_iter.collect::<Vec<_>>();
    /// assert_eq!(new_ids, vec![1, 2]);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, u32> = IdVec::new();
    /// // iterator has too many elements to fit!
    /// let result = v.try_extend(0..1000);
    /// assert!(result.is_err());
    /// ```
    pub fn try_extend<It: IntoIterator<Item = T>>(
        &mut self,
        iter: It,
    ) -> Result<IdRangeIter<I>, TryExtendError<I, T>> {
        let iter = iter.into_iter();
        let (size_min, _) = iter.size_hint();
        self.inner
            .try_reserve(size_min)
            .map_err(|_| TryExtendError::new())?;
        let start = self.count().to_value();
        for elem in iter {
            let _ = self.try_push(elem).map_err(|_| TryExtendError::new())?;
        }
        let end = self.count().to_value();
        Ok(IdRangeIter::from_indices(start, end))
    }

    /// Pushes all elements of an iterator onto the end of an `IdVec<I, T>`. Returns an iterator
    /// over the ids of all newly-inserted elements.
    ///
    /// # Panics
    ///
    /// Panics if the `IdVec<I, T>` does not have space to fit all the elements of `iter`. This
    /// error condition can happen either because the length of the `IdVec<I, T>` cannot grow large
    /// enough to accomodate the new elements from `iter` without exceeding the largest
    /// representable value of `I`, or because of an allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let new_ids_iter = v.extend(vec!["bar", "baz"]);
    /// let new_ids = new_ids_iter.collect::<Vec<_>>();
    /// assert_eq!(new_ids, vec![1, 2]);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, u32> = IdVec::new();
    /// // iterator has too many elements to fit!
    /// let result = v.extend(0..1000); // panics!
    /// ```
    #[must_use]
    pub fn extend<It: IntoIterator<Item = T>>(&mut self, iter: It) -> IdRangeIter<I> {
        match self.try_extend(iter) {
            Ok(new_ids) => new_ids,
            Err(err) => panic!("{err}"),
        }
    }

    /// Tries to clone and push all elements of a slice onto the end of an `IdVec<I, T>`. Returns an
    /// iterator over the ids of all newly-inserted elements.
    ///
    /// # Errors
    ///
    /// If the `IdVec<I, T>` does not have space to fit all the elements of `other`, returns an
    /// error. This error condition can happen either because the length of the `IdVec<I, T>` cannot
    /// grow large enough to accomodate the new elements from `other` without exceeding the largest
    /// representable value of `I`, or because of an allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    ///
    /// let result = v.try_extend_from_slice(&["bar", "baz"]);
    /// assert!(result.is_ok());
    /// let new_ids = result.unwrap().collect::<Vec<u32>>();
    /// assert_eq!(new_ids, vec![1, 2]);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..254 {
    ///     let _ = v.push("filler");
    /// }
    /// // 'v' now has 254 elements, which is one less than the largest value of 'u8'; we don't have
    /// // room to add two more!
    /// let result = v.try_extend_from_slice(&["foo", "bar"]);
    /// assert!(result.is_err());
    /// ```
    pub fn try_extend_from_slice(
        &mut self,
        other: &[T],
    ) -> Result<IdRangeIter<I>, TryExtendError<I, T>>
    where
        T: Clone,
    {
        let start = self.count().to_value();
        if let Some(other_len) = <I::Index as NumCast>::from(other.len()) {
            if let Some(end) = start.checked_add(&other_len) {
                if self.inner.try_reserve(other.len()).is_ok() {
                    self.inner.extend_from_slice(other);
                    return Ok(IdRangeIter::from_indices(start, end));
                }
            }
        }

        Err(TryExtendError::new())
    }

    /// Clones and pushes all elements of a slice onto the end of an `IdVec<I, T>`. Returns an
    /// iterator over the ids of all newly-inserted elements.
    ///
    /// # Panics
    ///
    /// Panics if the `IdVec<I, T>` does not have space to fit all the elements of `other`. This
    /// error condition can happen either because the length of the `IdVec<I, T>` cannot grow large
    /// enough to accomodate the new elements from `other` without exceeding the largest
    /// representable value of `I`, or because of an allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    ///
    /// let new_ids_iter = v.extend_from_slice(&["bar", "baz"]);
    /// let new_ids = new_ids_iter.collect::<Vec<u32>>();
    /// assert_eq!(new_ids, vec![1, 2]);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..254 {
    ///     let _ = v.push("filler");
    /// }
    /// // 'v' now has 254 elements, which is one less than the largest value of 'u8'; we don't have
    /// // room to add two more!
    /// let result = v.extend_from_slice(&["foo", "bar"]); // panics!
    /// ```
    #[must_use]
    pub fn extend_from_slice(&mut self, other: &[T]) -> IdRangeIter<I>
    where
        T: Clone,
    {
        match self.try_extend_from_slice(other) {
            Ok(iter) => iter,
            Err(err) => panic!("{err}"),
        }
    }

    /// Tries to push all elements of `other` onto the end of the `IdVec<I, T>`, leaving `other`
    /// empty. If it succeeds, returns an iterator over the ids of all the new elements which were
    /// inserted.
    ///
    /// # Errors
    ///
    /// If the `IdVec<I, T>` does not have space to fit all the elements of `other`, returns an
    /// error and leaves `other` unchanged. This error condition can happen either because the
    /// length of the `IdVec<I, T>` cannot grow large enough to accomodate the new elements from
    /// `other` without exceeding the largest representable value of `I`, or because of an
    /// allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    ///
    /// let result = v.try_append(&mut vec!["bar", "baz"]);
    /// assert!(result.is_ok());
    /// let new_ids = result.unwrap().collect::<Vec<u32>>();
    /// assert_eq!(new_ids, vec![1, 2]);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..254 {
    ///     let _ = v.push("filler");
    /// }
    /// // 'v' now has 254 elements, which is one less than the largest value of 'u8'; we don't have
    /// // room to add two more!
    /// let result = v.try_append(&mut vec!["foo", "bar"]);
    /// assert!(result.is_err());
    /// ```
    pub fn try_append(
        &mut self,
        other: &mut Vec<T>,
    ) -> Result<IdRangeIter<I>, TryExtendError<I, T>> {
        let start = self.count().to_value();
        if let Some(other_len) = <I::Index as NumCast>::from(other.len()) {
            if let Some(end) = start.checked_add(&other_len) {
                if self.inner.try_reserve(other.len()).is_ok() {
                    self.inner.append(other);
                    return Ok(IdRangeIter::from_indices(start, end));
                }
            }
        }

        Err(TryExtendError::new())
    }

    /// Pushes all elements of `other` onto the end of the `IdVec<I, T>`, leaving `other` empty.
    /// Returns an iterator over the ids of all the new elements which were inserted.
    ///
    /// # Panics
    ///
    /// Panics if the `IdVec<I, T>` does not have space to fit all the elements of `other`. This
    /// error condition can happen either because the length of the `IdVec<I, T>` cannot grow large
    /// enough to accomodate the new elements from `other` without exceeding the largest
    /// representable value of `I`, or because of an allocation failure in the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    ///
    /// let new_ids_iter = v.append(&mut vec!["bar", "baz"]);
    /// let new_ids = new_ids_iter.collect::<Vec<u32>>();
    /// assert_eq!(new_ids, vec![1, 2]);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..254 {
    ///     let _ = v.push("filler");
    /// }
    /// // 'v' now has 254 elements, which is one less than the largest value of 'u8'; we don't have
    /// // room to add two more!
    /// let result = v.append(&mut vec!["foo", "bar"]); // panics!
    /// ```
    #[must_use]
    pub fn append(&mut self, other: &mut Vec<T>) -> IdRangeIter<I> {
        match self.try_append(other) {
            Ok(iter) => iter,
            Err(err) => panic!("{err}"),
        }
    }

    /// Resizes the `IdVec<I, T>` in-place so that `self.count()` is equal to `new_count`.
    ///
    /// If `new_count` is greater than `self.count()`, the `IdVec<I, T>` is extended by the
    /// difference, with each additional slot filled with `value`. If `new_count` is less than
    /// `self.count()`, the `IdVec<I, T>` is simply truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v1: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v1.push("foo");
    /// assert_eq!(foo_id, 0);
    ///
    /// let mut v2: IdVec<u32, &str> = IdVec::new();
    /// let _ = v2.push("bar");
    /// let _ = v2.push("baz");
    /// let _ = v2.push("biz");
    ///
    /// let new_ids_iter = v1.resize(v2.count(), "quux");
    /// let new_ids = new_ids_iter.collect::<Vec<_>>();
    /// assert_eq!(v1.as_slice(), &["foo", "quux", "quux"]);
    /// assert_eq!(new_ids, vec![1, 2])
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let count_after_foo = v.count();
    /// let bar_id = v.push("bar");
    /// assert_eq!(bar_id, 1);
    /// let baz_id = v.push("baz");
    /// assert_eq!(baz_id, 2);
    ///
    /// let new_ids_iter = v.resize(count_after_foo, "quux");
    /// let new_ids = new_ids_iter.collect::<Vec<_>>();
    /// assert_eq!(v.as_slice(), &["foo"]);
    /// assert!(new_ids.is_empty());
    /// ```
    #[must_use]
    pub fn resize(&mut self, new_count: Count<I>, value: T) -> IdRangeIter<I>
    where
        T: Clone,
    {
        let old_count = self.count();
        if let Some(new_count_usize) = new_count.to_value().to_usize() {
            self.inner.resize(new_count_usize, value);
            if new_count > old_count {
                IdRangeIter::from_indices(old_count.to_value(), new_count.to_value())
            } else {
                IdRangeIter::empty()
            }
        } else {
            panic!("cannot resize IdVec: new_count overflows usize");
        }
    }

    /// Resizes the `IdVec<I, T>` in-place so that `self.count()` is equal to `new_count`. Returns
    /// an iterator (possibly empty) over the ids of any newly-inserted elements.
    ///
    /// If `new_count` is greater than `self.count()`, the `IdVec<I, T>` is extended by the
    /// difference, with each additional slot filled with the result of calling the closure `f`. The
    /// return values from `f` will end up in the `IdVec<I, T>` in the order they have been
    /// generated.
    ///
    /// If `new_count` is less than `self.count()`, the `IdVec<I, T>` is simply truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v1: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v1.push("foo");
    /// assert_eq!(foo_id, 0);
    ///
    /// let mut v2: IdVec<u32, &str> = IdVec::new();
    /// let _ = v2.push("bar");
    /// let _ = v2.push("baz");
    /// let _ = v2.push("biz");
    ///
    /// let new_ids_iter = v1.resize_with(v2.count(), || "quux");
    /// let new_ids = new_ids_iter.collect::<Vec<_>>();
    /// assert_eq!(v1.as_slice(), &["foo", "quux", "quux"]);
    /// assert_eq!(new_ids, vec![1, 2])
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let count_after_foo = v.count();
    /// let bar_id = v.push("bar");
    /// assert_eq!(bar_id, 1);
    /// let baz_id = v.push("baz");
    /// assert_eq!(baz_id, 2);
    ///
    /// let new_ids_iter = v.resize_with(count_after_foo, || "quux");
    /// let new_ids = new_ids_iter.collect::<Vec<_>>();
    /// assert_eq!(v.as_slice(), &["foo"]);
    /// assert!(new_ids.is_empty());
    /// ```
    #[must_use]
    pub fn resize_with<F>(&mut self, new_count: Count<I>, f: F) -> IdRangeIter<I>
    where
        F: FnMut() -> T,
    {
        let old_count = self.count();
        if let Some(new_count_usize) = new_count.to_value().to_usize() {
            self.inner.resize_with(new_count_usize, f);
            if new_count > old_count {
                IdRangeIter::from_indices(old_count.to_value(), new_count.to_value())
            } else {
                IdRangeIter::empty()
            }
        } else {
            panic!("cannot resize IdVec: new_count overflows usize");
        }
    }

    /// Removes an element from the end of the `IdVec<I, T>`, if it exists. Returns the id and value
    /// of the removed element, or `None` if the `IdVec<I, T>` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let bar_id = v.push("bar");
    /// assert_eq!(bar_id, 1);
    ///
    /// let pop1 = v.pop();
    /// assert_eq!(pop1, Some((1, "bar")));
    /// let pop2 = v.pop();
    /// assert_eq!(pop2, Some((0, "foo")));
    /// let pop3 = v.pop();
    /// assert_eq!(pop3, None);
    /// ```
    pub fn pop(&mut self) -> Option<(I, T)> {
        self.inner.pop().map(|value| {
            // This 'from_usize_unchecked' should never fail, as we should have previously enforced
            // the invariant that 'self.inner.len()' is representable as an 'I::Index' value.
            let index = I::Index::from_usize_unchecked(self.inner.len());
            (I::from_index(index), value)
        })
    }

    /// Clears the `IdVec<I, T>`, removing all values.
    ///
    /// Note that this has no effect on the allocated capacity of the underlying `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    /// Shortens the `IdVec<I, T>`, keeping the first `count` items and dropping the rest.
    ///
    /// If `count` is greater than `self.count()`, this has no effect.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let count_after_foo = v.count();
    /// let _ = v.push("bar");
    /// let _ = v.push("baz");
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    ///
    /// v.truncate(count_after_foo);
    /// assert_eq!(v.as_slice(), &["foo"]);
    /// ```
    pub fn truncate(&mut self, count: Count<I>) {
        let count_usize = count.to_value().to_usize().unwrap_or(usize::MAX);
        self.inner.truncate(count_usize)
    }

    /// Removes all elements after `start` from the vector in bulk, returning an iterator over the
    /// ids and values of all removed elements. If the iterator is dropped before being fully
    /// consumed, it drops the remaining removed elements.
    ///
    /// # Panics
    ///
    /// Panics if `start > self.count()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let count_after_foo = v.count();
    /// let bar_id = v.push("bar");
    /// assert_eq!(bar_id, 1);
    /// let baz_id = v.push("baz");
    /// assert_eq!(baz_id, 2);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    ///
    /// let drain_iter = v.drain_from(count_after_foo);
    /// let drain_items = drain_iter.collect::<Vec<_>>();
    /// assert_eq!(drain_items, vec![(1, "bar"), (2, "baz")]);
    /// assert_eq!(v.as_slice(), &["foo"]);
    /// ```
    pub fn drain_from(&mut self, start: Count<I>) -> Drain<'_, I, T> {
        let start_usize = start.to_value().to_usize().unwrap_or(usize::MAX);
        Drain {
            inner: EnumerateIds {
                inner: self.inner.drain(start_usize..),
                index: start.to_value(),
            },
        }
    }

    /// Removes all elements from the vector in bulk, returning an iterator over their ids and
    /// values. If the iterator is dropped before being fully consumed, it drops the remaining
    /// removed elements.
    ///
    /// Equivalent to `drain_from(Count::new())`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// assert_eq!(foo_id, 0);
    /// let bar_id = v.push("bar");
    /// assert_eq!(bar_id, 1);
    /// let baz_id = v.push("baz");
    /// assert_eq!(baz_id, 2);
    /// assert_eq!(v.as_slice(), &["foo", "bar", "baz"]);
    ///
    /// let drain_iter = v.drain_all();
    /// let drain_items = drain_iter.collect::<Vec<_>>();
    /// assert_eq!(drain_items, vec![(0, "foo"), (1, "bar"), (2, "baz")]);
    /// assert!(v.is_empty());
    /// ```
    pub fn drain_all(&mut self) -> Drain<'_, I, T> {
        self.drain_from(Count::new())
    }

    /// Returns a reference to the element with a given id, or `None` if the id is out of bounds.
    ///
    /// # See Also
    ///
    /// For a version of this function which panics on out-of-bounds ids instead of returning an
    /// `Option`, see [the `std::ops::Index` trait implementation for `IdVec<I, T>`.](IdVec::index)
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// assert_eq!(v.get(foo_id), Some(&"foo"));
    /// assert_eq!(v.get(bar_id), Some(&"bar"));
    /// assert_eq!(v.get(42), None);
    /// ```
    #[inline]
    pub fn get<J: Borrow<I>>(&self, id: J) -> Option<&T> {
        id.borrow()
            .to_index()
            .to_usize()
            .and_then(|idx| self.inner.get(idx))
    }

    /// Returns a mutable reference to the element with a given id, or `None` if the id is out of
    /// bounds.
    ///
    /// # See Also
    ///
    /// For a version of this function which panics on out-of-bounds ids instead of returning an
    /// `Option`, see [the `std::ops::IndexMut` trait implementation for `IdVec<I,
    /// T>`.](IdVec::index_mut)
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// let foo_mut_ref = v.get_mut(foo_id);
    /// assert!(foo_mut_ref.is_some());
    /// *foo_mut_ref.unwrap() = "baz";
    /// assert_eq!(v.as_slice(), &["baz", "bar"]);
    /// ```
    #[inline]
    pub fn get_mut<J: Borrow<I>>(&mut self, id: J) -> Option<&mut T> {
        id.borrow()
            .to_index()
            .to_usize()
            .and_then(|idx| self.inner.get_mut(idx))
    }

    /// Returns simultaneous mutable references to a pair of elements in the `IdVec<I, T>` with
    /// distinct ids, or `None` if the ids are the same.
    ///
    /// # Panics
    ///
    /// Panics if either `id1` or `id2` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// let pair = v.get_pair_mut(foo_id, bar_id);
    /// assert!(pair.is_some());
    /// let (foo_ref, bar_ref) = pair.unwrap();
    /// *foo_ref = "baz";
    /// *bar_ref = "biz";
    /// assert_eq!(v.as_slice(), &["baz", "biz"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// // cannot get two simultaneous mutable references to the same element:
    /// let pair = v.get_pair_mut(foo_id, foo_id);
    /// assert!(pair.is_none());
    /// ```
    pub fn get_pair_mut<J1: Borrow<I>, J2: Borrow<I>>(
        &mut self,
        id1: J1,
        id2: J2,
    ) -> Option<(&mut T, &mut T)> {
        let idx1 = id1
            .borrow()
            .to_index()
            .to_usize()
            .expect("id1 out of bounds");
        let idx2 = id2
            .borrow()
            .to_index()
            .to_usize()
            .expect("id2 out of bounds");
        match idx1.cmp(&idx2) {
            Ordering::Less => {
                let (slice1, slice2) = self.inner.split_at_mut(idx2);
                Some((&mut slice1[idx1], &mut slice2[0]))
            }
            Ordering::Greater => {
                let (slice2, slice1) = self.inner.split_at_mut(idx1);
                Some((&mut slice1[0], &mut slice2[idx2]))
            }
            Ordering::Equal => None,
        }
    }

    /// Swaps two elements in the `IdVec<I, T>`.
    ///
    /// # Panics
    ///
    /// Panics if either `id1` or `id2` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// v.swap(foo_id, bar_id);
    /// assert_eq!(v.as_slice(), &["bar", "foo"]);
    /// ```
    #[inline]
    pub fn swap<J1: Borrow<I>, J2: Borrow<I>>(&mut self, id1: J1, id2: J2) {
        match (
            id1.borrow().to_index().to_usize(),
            id2.borrow().to_index().to_usize(),
        ) {
            (Some(idx1), Some(idx2)) => {
                self.inner.swap(idx1, idx2);
            }
            _ => {
                panic!("cannot swap in IdVec: id value overflows usize");
            }
        }
    }

    /// Maps a function `f` over every element of the `IdVec<I, T>`, producing a new `IdVec` with
    /// the same id type.
    ///
    /// The elements of the `IdVec<I, T>` are moved into `f`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v1: IdVec<u32, i32> = IdVec::from_vec(vec![10, 20, 30]);
    /// let v2: IdVec<u32, i32> = v1.map(|_, x| x * x);
    /// assert_eq!(v2.as_slice(), &[100, 400, 900]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v1: IdVec<u32, &str> = IdVec::from_vec(vec!["foo", "bar", "baz"]);
    /// let v2: IdVec<u32, String> = v1.map(|id, s| format!("id {id}: {s}"));
    /// assert_eq!(v2.as_slice(), &["id 0: foo", "id 1: bar", "id 2: baz"]);
    /// ```
    pub fn map<U, F>(self, mut f: F) -> IdVec<I, U>
    where
        F: FnMut(I, T) -> U,
    {
        IdVec::from_vec(self.into_iter().map(|(id, elem)| f(id, elem)).collect())
    }

    /// Maps a function `f` over every element of the `IdVec<I, T>`, producing a new `IdVec` with
    /// the same id type.
    ///
    /// The elements of the `IdVec<I, T>` are passed to `f` by reference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v1: IdVec<u32, i32> = IdVec::from_vec(vec![10, 20, 30]);
    /// let v2: IdVec<u32, i32> = v1.map_refs(|_, &x| x * x);
    /// assert_eq!(v2.as_slice(), &[100, 400, 900]);
    /// assert_eq!(v1.as_slice(), &[10, 20, 30]); // v1 has not been moved
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v1: IdVec<u32, &str> = IdVec::from_vec(vec!["foo", "bar", "baz"]);
    /// let v2: IdVec<u32, String> = v1.map_refs(|id, &s| format!("id {id}: {s}"));
    /// assert_eq!(v2.as_slice(), &["id 0: foo", "id 1: bar", "id 2: baz"]);
    /// assert_eq!(v1.as_slice(), &["foo", "bar", "baz"]); // v1 has not been moved
    /// ```
    pub fn map_refs<U, F>(&self, mut f: F) -> IdVec<I, U>
    where
        F: FnMut(I, &T) -> U,
    {
        IdVec::from_vec(self.iter().map(|(id, elem)| f(id, elem)).collect())
    }

    /// Tries mapping a fallible function `f` over every element of the `IdVec<I, T>`, producing a
    /// new `IdVec` with the same id type.
    ///
    /// The elements of the `IdVec<I, T>` are moved into `f`.
    ///
    /// # Errors
    ///
    /// Returns the first error from `f`, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let strings: IdVec<u32, &str> = IdVec::from_vec(vec!["10", "20", "30"]);
    /// let numbers: Result<IdVec<u32, i32>, _> = strings.try_map(|_, s| s.parse::<i32>());
    /// assert!(numbers.is_ok());
    /// assert_eq!(numbers.unwrap().as_slice(), &[10, 20, 30]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let strings: IdVec<u32, &str> = IdVec::from_vec(vec!["10", "20", "banana"]);
    /// let numbers: Result<IdVec<u32, i32>, _> = strings.try_map(|_, s| s.parse::<i32>());
    /// assert!(numbers.is_err());
    /// ```
    pub fn try_map<U, E, F>(self, mut f: F) -> Result<IdVec<I, U>, E>
    where
        F: FnMut(I, T) -> Result<U, E>,
    {
        Ok(IdVec::from_vec(
            self.into_iter()
                .map(|(id, elem)| f(id, elem))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    /// Tries mapping a fallible function `f` over every element of the `IdVec<I, T>`, producing a
    /// new `IdVec` with the same id type.
    ///
    /// The elements of the `IdVec<I, T>` are passed to `f` by reference.
    ///
    /// # Errors
    ///
    /// Returns the first error from `f`, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let strings: IdVec<u32, &str> = IdVec::from_vec(vec!["10", "20", "30"]);
    /// let numbers: Result<IdVec<u32, i32>, _> = strings.try_map_refs(|_, &s| s.parse::<i32>());
    /// assert!(numbers.is_ok());
    /// assert_eq!(numbers.unwrap().as_slice(), &[10, 20, 30]);
    /// assert_eq!(strings.as_slice(), &["10", "20", "30"]); // 'strings' has not been moved
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let strings: IdVec<u32, &str> = IdVec::from_vec(vec!["10", "20", "banana"]);
    /// let numbers: Result<IdVec<u32, i32>, _> = strings.try_map_refs(|_, &s| s.parse::<i32>());
    /// assert!(numbers.is_err());
    /// assert_eq!(strings.as_slice(), &["10", "20", "banana"]); // 'strings' has not been moved
    /// ```
    pub fn try_map_refs<U, E, F>(&self, mut f: F) -> Result<IdVec<I, U>, E>
    where
        F: FnMut(I, &T) -> Result<U, E>,
    {
        Ok(IdVec::from_vec(
            self.iter()
                .map(|(id, elem)| f(id, elem))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }

    /// Returns an iterator over ids and elements of the `IdVec<I, T>`. The elements are returned
    /// by immutable reference.
    ///
    /// Calling `.iter()` is equivalent to calling `.into_iter()` on an `&IdVec<I, T>` reference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// let iter = v.iter();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec![(foo_id, &"foo"), (bar_id, &"bar")]);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<I, T> {
        Iter {
            inner: EnumerateIds {
                inner: self.inner.iter(),
                index: I::Index::zero(),
            },
        }
    }

    /// Returns an iterator over ids and elements of the `IdVec<I, T>`. The elements are returned by
    /// mutable reference.
    ///
    /// Calling `.iter_mut()` is equivalent to calling `.into_iter()` on an `&mut IdVec<I, T>`
    /// reference.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// for (_, elem) in v.iter_mut() {
    ///     *elem = "baz";
    /// }
    /// assert_eq!(v.as_slice(), &["baz", "baz"]);
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<I, T> {
        IterMut {
            inner: EnumerateIds {
                inner: self.inner.iter_mut(),
                index: I::Index::zero(),
            },
        }
    }

    /// Returns an iterator over the elements of the `IdVec<I, T>`. The elements are returned by
    /// immutable reference.
    ///
    /// Calling `.values()` is equivalent to calling `.as_slice().iter()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// let iter = v.values();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec![&"foo", &"bar"]);
    /// ```
    #[inline]
    pub fn values(&self) -> std::slice::Iter<'_, T> {
        self.as_slice().iter()
    }

    /// Returns an iterator over the elements of the `IdVec<I, T>`. The elements are returned by
    /// mutable reference.
    ///
    /// Calling `.values_mut()` is equivalent to calling `.as_mut_slice().iter_mut()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// for elem in v.values_mut() {
    ///     *elem = "baz";
    /// }
    /// assert_eq!(v.as_slice(), &["baz", "baz"]);
    /// ```
    #[inline]
    pub fn values_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.as_mut_slice().iter_mut()
    }

    /// Returns an iterator over the elements of the `IdVec<I, T>`. The elements are moved out of
    /// the `IdVec<I, T>`.
    ///
    /// Calling `.into_values()` is equivalent to calling `.into_vec().into_iter()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// let iter = v.into_values();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec!["foo", "bar"]);
    /// ```
    #[inline]
    pub fn into_values(self) -> std::vec::IntoIter<T> {
        self.into_vec().into_iter()
    }

    /// Returns the capacity of the underlying vector.
    ///
    /// This is a wrapper around [`Vec::capacity`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let v: IdVec<u32, i32> = IdVec::with_capacity(4);
    /// assert_eq!(v.capacity(), 4);
    /// ```
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Tries to reserve additional capacity for at least `additional` more elements to be inserted
    /// in the given `IdVec<I, T>`.
    ///
    /// This is a wrapper around [`Vec::try_reserve`].
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve(additional)
    }

    /// Reserves capacity for at least `additional` more elements to be inserted in the given
    /// `IdVec<I, T>`.
    ///
    /// This is a wrapper around [`Vec::reserve`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// v.reserve(10);
    /// assert!(v.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Tries to reserve additional capacity for exactly `additional` more elements to be inserted
    /// in the given `IdVec<I, T>`.
    ///
    /// This is a wrapper around [`Vec::try_reserve_exact`].
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.inner.try_reserve_exact(additional)
    }

    /// Reserves capacity for exactly `additional` more elements to be inserted in the given
    /// `IdVec<I, T>`.
    ///
    /// This is a wrapper around [`Vec::reserve_exact`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// v.reserve_exact(10);
    /// assert!(v.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Shrinks the capacity of the `IdVec<I, T>` as much as possible.
    ///
    /// This is a wrapper around [`Vec::shrink_to_fit`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::with_capacity(10);
    /// v.push("foo");
    /// v.push("bar");
    /// v.shrink_to_fit();
    /// assert!(v.capacity() >= 2);
    /// assert_eq!(v.as_slice(), &["foo", "bar"]); // elements are still there
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit()
    }

    /// Shrinks the capacity of the `IdVec<I, T>` with a lower bound.
    ///
    /// This is a wrapper around [`Vec::shrink_to`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::with_capacity(10);
    /// v.push("foo");
    /// v.push("bar");
    /// assert_eq!(v.capacity(), 10);
    /// v.shrink_to(4);
    /// assert!(v.capacity() >= 4);
    /// v.shrink_to(0);
    /// assert!(v.capacity() >= 2);
    /// assert_eq!(v.as_slice(), &["foo", "bar"]); // elements are still there
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.inner.shrink_to(min_capacity);
    }

    /// Tries to convert a `Vec<T>` into an `IdVec<I, T>`.
    ///
    /// # Errors
    ///
    /// If the `Vec<T>` has length greater than the largest representable value of `I`, returns an
    /// error containing the original `Vec<T>` unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let plain_vec = vec!["foo", "bar"];
    /// let id_vec: IdVec<u32, &str> = IdVec::try_from_vec(plain_vec).unwrap();
    /// assert_eq!(id_vec.as_slice(), &["foo", "bar"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let big_vec: Vec<i32> = (0..1000).collect();
    /// let result = IdVec::<u8, i32>::try_from_vec(big_vec);
    /// // 'big_vec' is too big to convert to an 'IdVec<u8, i32>':
    /// assert!(result.is_err());
    /// // we can use 'into_vec' to extract the original 'Vec<T>' passed to 'try_from_vec':
    /// assert!(result.unwrap_err().into_vec() == (0..1000).collect::<Vec<_>>());
    /// ```
    pub fn try_from_vec(inner: Vec<T>) -> Result<Self, TryFromVecError<I, T>> {
        if <I::Index as NumCast>::from(inner.len()).is_some() {
            Ok(IdVec {
                phantom: PhantomData,
                inner,
            })
        } else {
            Err(TryFromVecError::new(inner))
        }
    }

    /// Converts a `Vec<T>` into an `IdVec<I, T>`.
    ///
    /// # Panics
    ///
    /// Panics if the `Vec<T>` has length greater than the largest representable value of `I`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let plain_vec = vec!["foo", "bar"];
    /// let id_vec: IdVec<u32, &str> = IdVec::from_vec(plain_vec);
    /// assert_eq!(id_vec.as_slice(), &["foo", "bar"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let big_vec: Vec<i32> = (0..1000).collect();
    /// // 'big_vec' is too big to convert to an 'IdVec<u8, i32>':
    /// let result = IdVec::<u8, i32>::from_vec(big_vec); // panics!
    /// ```
    pub fn from_vec(inner: Vec<T>) -> Self {
        match Self::try_from_vec(inner) {
            Ok(result) => result,
            Err(err) => panic!("{err}"),
        }
    }

    /// Converts the `IdVec<I, T>` into a plain `Vec<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// assert_eq!(v.into_vec(), vec!["foo", "bar"]);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }

    /// Returns a slice of the underlying vector of the `IdVec<I, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// assert_eq!(v.as_slice(), &["foo", "bar"]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }

    /// Returns a mutable slice of the underlying vector of the `IdVec<I, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let _ = v.push("foo");
    /// let _ = v.push("bar");
    /// assert_eq!(v.as_mut_slice(), &["foo", "bar"]);
    /// v.as_mut_slice()[0] = "baz";
    /// assert_eq!(v.as_mut_slice(), &["baz", "bar"]);
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.inner
    }
}

#[derive(Debug)]
struct EnumerateIds<I: Id, It> {
    inner: It,
    index: I::Index,
}

impl<I: Id, It> Iterator for EnumerateIds<I, It>
where
    It: Iterator + ExactSizeIterator + DoubleEndedIterator,
{
    type Item = (I, It::Item);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|elem| {
            let id = I::from_index(self.index);
            self.index = self.index + I::Index::one();
            (id, elem)
        })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    #[inline]
    fn count(self) -> usize {
        self.inner.count()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        // This leaves 'self.index' in an incorrect state when 'n' exceeds the number of elements
        // remaining in the iterator, but that's okay, because in that case the iterator is done
        // yielding elements anyway.
        self.inner.nth(n).map(|elem| {
            let elem_index = self.index + I::Index::from_usize_unchecked(n);
            self.index = elem_index + I::Index::one();
            (I::from_index(elem_index), elem)
        })
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<I: Id, It> ExactSizeIterator for EnumerateIds<I, It>
where
    It: Iterator + ExactSizeIterator + DoubleEndedIterator,
{
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<I: Id, It> FusedIterator for EnumerateIds<I, It> where
    It: Iterator + ExactSizeIterator + DoubleEndedIterator + FusedIterator
{
}

impl<I: Id, It> DoubleEndedIterator for EnumerateIds<I, It>
where
    It: Iterator + ExactSizeIterator + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|elem| {
            let new_len = self.inner.len();
            let id = I::from_index(self.index + I::Index::from_usize_unchecked(new_len));
            (id, elem)
        })
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.inner.nth_back(n).map(|elem| {
            let new_len = self.inner.len();
            let id = I::from_index(self.index + I::Index::from_usize_unchecked(new_len));
            (id, elem)
        })
    }
}

macro_rules! impl_iter_wrapper {
    (
        $(#[$attr:meta])*
        $name:ident { $($generic:tt)* } => $item_ty:ty
        where { $($bound:tt)* }
        { inner: $inner_ty:ty, }
    ) => {
        $(#[$attr])*
        #[derive(Debug)]
        pub struct $name<$($generic)*> where $($bound)* {
            inner: $inner_ty,
        }

        impl<$($generic)*> Iterator for $name<$($generic)*> where $($bound)* {
            type Item = $item_ty;
            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.inner.next()
            }
            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.inner.size_hint()
            }
            #[inline]
            fn count(self) -> usize {
                self.inner.count()
            }
            #[inline]
            fn nth(&mut self, n: usize) -> Option<Self::Item> {
                self.inner.nth(n)
            }
            #[inline]
            fn last(self) -> Option<Self::Item> {
                self.inner.last()
            }
        }

        impl<$($generic)*> ExactSizeIterator for $name<$($generic)*> where $($bound)* {
            #[inline]
            fn len(&self) -> usize {
                self.inner.len()
            }
        }

        impl<$($generic)*> FusedIterator for $name<$($generic)*> where $($bound)* {}

        impl<$($generic)*> DoubleEndedIterator for $name<$($generic)*> where $($bound)* {
            #[inline]
            fn next_back(&mut self) -> Option<Self::Item> {
                self.inner.next_back()
            }
            #[inline]
            fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
                self.inner.nth_back(n)
            }
        }
    };
}

impl_iter_wrapper! {
    /// A draining iterator for [`IdVec<I, T>`].
    ///
    /// This type is returned by [`IdVec::drain_from`] and [`IdVec::drain_all`]. See those
    /// functions' documentation for more details.
    Drain { 'a, I, T } => (I, T) where { I: Id } {
        inner: EnumerateIds<I, std::vec::Drain<'a, T>>,
    }
}

impl_iter_wrapper! {
    /// An iterator for [`IdVec<I, T>`] which returns values by immutable reference.
    ///
    /// This type is returned by [`IdVec::iter`]. See that function's documentation for more
    /// details.
    Iter { 'a, I, T } => (I, &'a T) where { I: Id } {
        inner: EnumerateIds<I, std::slice::Iter<'a, T>>,
    }
}

impl_iter_wrapper! {
    /// An iterator for [`IdVec<I, T>`] which returns values by mutable reference.
    ///
    /// This type is returned by [`IdVec::iter_mut`]. See that function's documentation for more
    /// details.
    IterMut { 'a, I, T } => (I, &'a mut T) where { I: Id } {
        inner: EnumerateIds<I, std::slice::IterMut<'a, T>>,
    }
}

impl_iter_wrapper! {
    /// An iterator for [`IdVec<I, T>`] which returns values by move.
    ///
    /// This type is returned by [`IdVec::into_iter`](struct.IdVec.html#impl-IntoIterator-2). See
    /// that function's documentation for more details.
    IntoIter { I, T } => (I, T) where { I: Id } {
        inner: EnumerateIds<I, std::vec::IntoIter<T>>,
    }
}

impl<'a, I: Id, T> IntoIterator for &'a IdVec<I, T> {
    type Item = (I, &'a T);
    type IntoIter = Iter<'a, I, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, I: Id, T> IntoIterator for &'a mut IdVec<I, T> {
    type Item = (I, &'a mut T);
    type IntoIter = IterMut<'a, I, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, I: Id, T> IntoIterator for IdVec<I, T> {
    type Item = (I, T);
    type IntoIter = IntoIter<I, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: EnumerateIds {
                inner: self.inner.into_iter(),
                index: I::Index::zero(),
            },
        }
    }
}

#[cfg(test)]
mod iter_test {
    use crate::IdVec;

    #[test]
    fn test_size_hint() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2]);
        assert_eq!(v.iter().size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_count() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2]);
        assert_eq!(v.iter().count(), 3);
    }

    #[test]
    fn test_nth() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2]);
        let mut it = v.iter();
        assert_eq!(it.nth(1), Some((1, &1)));
        assert_eq!(it.next(), Some((2, &2)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_last() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2]);
        assert_eq!(v.iter().last(), Some((2, &2)));
    }

    #[test]
    fn test_len() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2]);
        assert_eq!(v.iter().len(), 3);
    }

    #[test]
    fn test_next_back() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2]);
        let mut it = v.iter();
        assert_eq!(it.next_back(), Some((2, &2)));
        assert_eq!(it.next_back(), Some((1, &1)));
        assert_eq!(it.next(), Some((0, &0)));
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
    }

    #[test]
    fn test_nth_back() {
        let v = IdVec::<u32, _>::from_vec(vec![0, 1, 2, 3]);
        let mut it = v.iter();
        assert_eq!(it.nth_back(1), Some((2, &2)));
        assert_eq!(it.next_back(), Some((1, &1)));
        assert_eq!(it.next(), Some((0, &0)));
        assert_eq!(it.next(), None);
    }
}

impl<I: Id, T, J: Borrow<I>> Index<J> for IdVec<I, T> {
    type Output = T;

    /// Returns a reference to the element with a given id.
    ///
    /// # Panics
    ///
    /// Panics if `id` is out of bounds.
    ///
    /// # See Also
    ///
    /// For a version of this function which returns an `Option` instead of panicking on
    /// out-of-bounds ids, see [`IdVec::get`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// assert_eq!(v[foo_id], "foo");
    /// assert_eq!(v[bar_id], "bar");
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let val = v[42]; // panics!
    /// ```
    #[inline]
    fn index(&self, id: J) -> &Self::Output {
        match id.borrow().to_index().to_usize() {
            Some(index) => &self.inner[index],
            None => panic!("cannot index IdVec: id overflows usize"),
        }
    }
}

impl<I: Id, T, J: Borrow<I>> IndexMut<J> for IdVec<I, T> {
    /// Returns a mutable reference to the element with a given id.
    ///
    /// # Panics
    ///
    /// Panics if `id` it out of bounds.
    ///
    /// # See Also
    ///
    /// For a version of this function which returns an `Option` instead of panicking on
    /// out-of-bounds ids, see [`IdVec::get_mut`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let foo_id = v.push("foo");
    /// let bar_id = v.push("bar");
    /// v[foo_id] = "baz";
    /// v[bar_id] = "biz";
    /// assert_eq!(v.as_slice(), &["baz", "biz"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u32, &str> = IdVec::new();
    /// let val_ref = &mut v[42]; // panics!
    /// ```
    #[inline]
    fn index_mut(&mut self, id: J) -> &mut Self::Output {
        match id.borrow().to_index().to_usize() {
            Some(index) => &mut self.inner[index],
            None => panic!("cannot index IdVec: id overflows usize"),
        }
    }
}

impl<I: Id + Debug, T: Debug> Debug for IdVec<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// An error indicating that a [`Vec<T>`] is too large to be converted into an [`IdVec<I, T>`].
///
/// This error can be returned from [`IdVec::try_from_vec`]. See that function's documentation for
/// more details.
#[derive(Clone, Debug)]
pub struct TryFromVecError<I: Id, T> {
    phantom: PhantomData<I>,
    vec: Vec<T>,
}

impl<I: Id, T> TryFromVecError<I, T> {
    fn new(vec: Vec<T>) -> Self {
        TryFromVecError {
            phantom: PhantomData,
            vec,
        }
    }

    /// Extracts the original [`Vec<T>`] which was to be converted into an [`IdVec<I, T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let big_vec: Vec<i32> = (0..1000).collect();
    /// let result = IdVec::<u8, i32>::try_from_vec(big_vec);
    /// // 'big_vec' is too big to convert to an 'IdVec<u8, i32>':
    /// assert!(result.is_err());
    /// // we can use 'into_vec' to extract the original 'Vec<T>' passed to 'try_from_vec':
    /// assert!(result.unwrap_err().into_vec() == (0..1000).collect::<Vec<_>>());
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.vec
    }
}

impl<I: Id, T> Display for TryFromVecError<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot convert Vec to IdVec: vector length {} overflows {}",
            self.vec.len(),
            std::any::type_name::<I>()
        )
    }
}

impl<I: Id + Debug, T: Debug> std::error::Error for TryFromVecError<I, T> {}

/// An error indicating that a value could not be inserted into an [`IdVec<I, T>`].
///
/// This error can be returned from [`IdVec::try_push`]. See that function's documentation for more
/// details.
#[derive(Clone, Debug)]
pub struct TryPushError<I: Id, T> {
    phantom: PhantomData<I>,
    value: T,
}

impl<I: Id, T> TryPushError<I, T> {
    fn new(value: T) -> Self {
        TryPushError {
            phantom: PhantomData,
            value,
        }
    }

    /// Extracts the original value which was to be pushed into the [`IdVec<I, T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdVec;
    /// let mut v: IdVec<u8, &str> = IdVec::new();
    /// for _ in 0..255 {
    ///     let result = v.try_push("filler");
    ///     assert!(result.is_ok());
    /// }
    /// // 'v' now has 255 elements, which is the largest value of 'u8'; we can't add any more!
    /// let result = v.try_push("foo");
    /// assert!(result.is_err());
    /// // we can use 'into_value' to extract the original value passed to 'try_push':
    /// assert!(result.unwrap_err().into_value() == "foo");
    /// ```
    pub fn into_value(self) -> T {
        self.value
    }
}

impl<I: Id, T> Display for TryPushError<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot push to IdVec: length overflows {}",
            std::any::type_name::<I>()
        )
    }
}

impl<I: Id + Debug, T: Debug> std::error::Error for TryPushError<I, T> {}

/// An error indicating that an [`IdVec<I, T>`] could not be extended.
///
/// This error can be returned from [`IdVec::try_extend`], [`IdVec::try_extend_from_slice`], and
/// [`IdVec::try_append`]. See those functions' documentation for more details.
#[derive(Clone, Debug)]
pub struct TryExtendError<I: Id, T> {
    phantom: PhantomData<(I, T)>,
}

impl<I: Id, T> TryExtendError<I, T> {
    fn new() -> Self {
        TryExtendError {
            phantom: PhantomData,
        }
    }
}

impl<I: Id, T> Display for TryExtendError<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "cannot extend IdVec: length overflows {}",
            std::any::type_name::<I>()
        )
    }
}

impl<I: Id + Debug, T: Debug> std::error::Error for TryExtendError<I, T> {}
