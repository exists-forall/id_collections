//! The [`IdMap<I, T>`] structure and related types.

use std::{
    borrow::Borrow,
    fmt::{Debug, Display},
    hash::Hash,
    iter::FusedIterator,
    marker::PhantomData,
    ops::Index,
};

use num_traits::{Bounded, NumCast, One, ToPrimitive, Zero};

use crate::{
    count::Count,
    id::{Id, ToPrimIntUnchecked},
    id_vec::{self, IdVec},
};

/// A map-like data structure with strongly-typed integer keys, backed by a vector.
///
/// An `IdMap<I, T>` is a key-value map data structure designed for use with key types which
/// implement the [`Id`] trait. You can define your own types implementing [`Id`] and use them with
/// [`IdMap`]:
///
/// ```
/// use id_collections::{IdMap, id_type};
///
/// #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct CityId(u32);
///
/// let mut cities: IdMap<CityId, &str> = IdMap::new();
///
/// let toronto_id = CityId(1);
/// let beijing_id = CityId(3);
/// let são_paulo_id = CityId(5);
///
/// cities.insert(toronto_id, "Toronto");
/// cities.insert(beijing_id, "Beijing");
/// cities.insert(são_paulo_id, "São Paulo");
///
/// assert_eq!(cities[toronto_id], "Toronto");
/// assert_eq!(cities[beijing_id], "Beijing");
/// assert_eq!(cities[são_paulo_id], "São Paulo");
/// ```
///
/// The `IdMap<I, T>` type exposes an API similar to [`HashMap<I, T>`](std::collections::HashMap) or
/// [`BTreeMap<I, T>`](std::collections::BTreeMap). However, `IdMap<I, T>` is designed with very
/// different performance tradeoffs in mind than [`HashMap`](std::collections::HashMap) or
/// [`BTreeMap`](std::collections::BTreeMap). **Internally, an `IdMap<I, T>` is represented by a
/// vector whose length is at least as large as the largest key in the map.** Indexing an
/// `IdMap<I, T>` corresponds to directly indexing this vector. This means that accessing
/// individual elements in an `IdMap<I, T>` can be very fast. However, this design also means that
/// if your keys are sparsely distributed over a large range, using an `IdMap<I, T>` can be much
/// less efficient in terms of both memory usage and runtime than using a
/// [`HashMap`](std::collections::HashMap) or a
/// [`BTreeMap`](std::collections::BTreeMap).
///
/// # ⚠️ Performance Hazards: When Not to Use `IdMap<I, T>`
///
/// An `IdMap<I, T>` is internally represented by a vector where each element corresponds to a
/// (possibly vacant) entry in the map. Keys are mapped 1:1 to indices in this vector, and the
/// memory usage of an `IdMap<I, T>` is proportional to its **largest key**. This means that
/// inserting a single entry in an `IdMap<I, T>` can allocate a large amount of memory if the
/// key is large:
///
/// ```
/// # use id_collections::{IdMap, id_type};
/// #
/// # #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// # struct CityId(u32);
/// #
/// let mut cities: IdMap<CityId, &str> = IdMap::new();
///
/// // allocates space for at least 1000 entries!
/// cities.insert(CityId(999), "Berlin");
/// ```
///
/// Moreover, some operations, like iterating over all values returned by [`IdMap::iter`], take
/// time proportional to the largest key in the map, even if most entries prior to the entry
/// with the largest key are vacant:
///
/// ```
/// # use id_collections::{IdMap, id_type};
/// #
/// # #[id_type]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// # struct CityId(u32);
/// #
/// let mut cities: IdMap<CityId, &str> = IdMap::new();
/// cities.insert(CityId(999), "Berlin");
///
/// // this loop takes time roughly equivalent to iterating over 1000 occupied entries!
/// let mut city_names = Vec::new();
/// for (_, &city_name) in cities.iter() {
///     city_names.push(city_name);
/// }
/// assert_eq!(city_names, vec!["Berlin"]);
/// ```
///
/// In general, `IdMap<I, T>` is intended for use with *dense key distributions*, in which all or
/// almost all keys up to a certain value will eventually be inserted into the map.
///
/// - **You should consider using `IdMap<I, T>` if**:
///     - You're writing an algorithm which will eventually fill in all keys in the map up to a
///       certain value, possibly out of order.
///     - You have relatively sparse keys, but want very fast indexing at the cost of additional
///       memory usage and iteration time.
/// - **You might not want not use `IdMap<I, T>` if**:
///     - You're filling in all keys up a certain value *in ascending order*; an `IdMap<I, T>` will
///       work for this, but an [`IdVec<I, T>`](crate::IdVec) may be an even better choice.
///     - Your keys are sparsely distributed over a large range, or you smallest key is much
///       larger than zero. You should probably use a [`HashMap<I, T>`](std::collections::HashMap)
///       or a [`BTreeMap<I, T>`](std::collections::BTreeMap) in this case.
///
/// # Operations
///
/// - **Creating a new `IdMap<I, T>`**:
///     - [`IdMap::new`]
///     - [`IdMap::with_capacity`]
///     - [`IdMap::from_iter`]
/// - **Accessing the size of an `IdMap<I, T>`**:
///     - [`IdMap::len`]
///     - [`IdMap::is_empty`]
/// - **Adding entries to an `IdMap<I, T>`**:
///     - [`IdMap::insert`]
///     - [`IdMap::try_insert`]
///     - [`IdMap::insert_vacant`]
///     - [`IdMap::entry`] (using [`Entry::or_insert`], etc.)
///     - [`IdMap::extend`]
/// - **Removing entries from an `IdMap<I, T>`**:
///     - [`IdMap::remove`]
///     - [`IdMap::clear`]
///     - [`IdMap::drain`]
///     - [`IdMap::entry`] (using [`OccupiedEntry::remove`])
///     - [`IdMap::retain`]
/// - **Accessing entries of an `IdMap<I, T>`**:
///     - [`IdMap::contains_key`]
///     - [`IdMap::get`]
///     - [`IdMap::index`] (the `collection[i]` operator)
///     - [`IdMap::get_mut`]
///     - [`IdMap::get_pair_mut`]
///     - [`IdMap::entry`] (using [`Entry::and_modify`], etc.)
/// - **Iterating over an `IdMap<I, T>`**:
///     - [`IdMap::iter`]
///     - [`IdMap::iter_mut`]
///     - [`IdMap::into_iter`](struct.IdMap.html#impl-IntoIterator-2)
///     - [`IdMap::keys`]
///     - [`IdMap::values`]
///     - [`IdMap::values_mut`]
///     - [`IdMap::into_values`]
/// - **Converting between `IdMap<I, T>` and [`IdVec<I, T>`]**:
///     - [`IdMap::from(IdVec<I, T>)`](IdMap::from)
///     - [`IdMap::try_to_id_vec`]
///     - [`IdMap::to_id_vec`]
/// - **Managing allocations**:
///     - [`IdMap::capacity`]
///     - [`IdMap::try_reserve`]
///     - [`IdMap::reserve`]
///     - [`IdMap::shrink_to_fit`]
///     - [`IdMap::shrink_to`]
///
/// # Serde Support
///
/// When the `serde` Cargo feature is enabled, `IdMap<I, T>` can be serialized and deserialized
/// using [Serde](https://serde.rs/). An `IdMap<I, T>` is serialized as a sequence of `(key, value)`
/// pairs in ascending order by key:
///
/// ```
/// # #[cfg(feature = "serde")]
/// # {
/// use id_collections::{IdMap, id_type};
///
/// #[id_type(serde = true)]
/// # #[is_doctest_b244a423_69a4_4e0c_9697_283f66a8ba88]
/// struct CityId(u32);
///
/// let mut cities: IdMap<CityId, &str> = IdMap::new();
///
/// cities.insert(CityId(1), "Toronto");
/// cities.insert(CityId(3), "Beijing");
/// cities.insert(CityId(5), "São Paulo");
///
/// let serialized = serde_json::to_string(&cities).unwrap();
/// assert_eq!(&serialized, r#"[[1,"Toronto"],[3,"Beijing"],[5,"São Paulo"]]"#);
/// # }
/// ```
#[derive(Clone)]
pub struct IdMap<I: Id, T> {
    inner: IdVec<I, Option<T>>,
    num_present: I::Index,
}

impl<I: Id, T: PartialEq> PartialEq for IdMap<I, T> {
    fn eq(&self, other: &Self) -> bool {
        if self.num_present != other.num_present {
            return false;
        }
        let common_len = self.inner.len().min(other.inner.len());
        self.inner.as_slice()[..common_len] == other.inner.as_slice()[..common_len]
    }
}

impl<I: Id, T: Eq> Eq for IdMap<I, T> {}

impl<I: Id, T: Hash> Hash for IdMap<I, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        for pair in self {
            pair.hash(state);
        }
    }
}

impl<I: Id + Debug, T: Debug> Debug for IdMap<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

#[cfg(feature = "serde")]
impl<I: Id + serde::Serialize, T: serde::Serialize> serde::Serialize for IdMap<I, T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeSeq;
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for (id, value) in self {
            seq.serialize_element(&(id, value))?;
        }
        seq.end()
    }
}

#[cfg(feature = "serde")]
impl<'de, I: Id + serde::Deserialize<'de>, T: serde::Deserialize<'de>> serde::Deserialize<'de>
    for IdMap<I, T>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        use serde::de::Error;

        struct Visitor<I: Id, T> {
            phantom: PhantomData<IdMap<I, T>>,
        }

        impl<'de, I: Id + serde::Deserialize<'de>, T: serde::Deserialize<'de>>
            serde::de::Visitor<'de> for Visitor<I, T>
        {
            type Value = IdMap<I, T>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("an IdMap represented by a sequence of id-value pairs")
            }

            fn visit_seq<A>(self, mut access: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                let mut map = IdMap::with_capacity(access.size_hint().unwrap_or(0));
                let mut prev_id = None;
                while let Some((id, value)) = access.next_element()? as Option<(I, T)> {
                    if Some(id) <= prev_id {
                        return Err(A::Error::custom(
                            "id values must be given in ascending order",
                        ));
                    }
                    prev_id = Some(id);
                    map.insert(id, value);
                }
                Ok(map)
            }
        }

        deserializer.deserialize_seq(Visitor {
            phantom: PhantomData,
        })
    }
}

#[cfg(all(test, feature = "serde"))]
mod serde_test {
    use crate::{id_type, IdMap};

    #[test]
    fn test_deserialize() {
        #[id_type(serde = true)]
        struct TestId(u32);

        let serialized = r#"[[1,"foo"],[3,"bar"],[5,"baz"]]"#;
        let map: IdMap<TestId, String> = serde_json::from_str(serialized).unwrap();
        assert_eq!(
            map,
            IdMap::from_iter([
                (TestId(1), "foo".to_owned()),
                (TestId(3), "bar".to_owned()),
                (TestId(5), "baz".to_owned()),
            ])
        );
    }

    #[test]
    fn test_deserialize_invalid_order() {
        #[id_type(serde = true)]
        struct TestId(u32);

        let serialized_1 = r#"[[3,"bar"],[5,"foo"],[1,"baz"]]"#;
        assert!(serde_json::from_str::<IdMap<TestId, String>>(serialized_1).is_err());

        let serialized_2 = r#"[[1,"foo"],[1,"foo"]]"#;
        assert!(serde_json::from_str::<IdMap<TestId, String>>(serialized_2).is_err());
    }
}

impl<I: Id, T> Default for IdMap<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: Id, T> IdMap<I, T> {
    /// Constructs a new, empty `IdMap<I, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let map: IdMap<u32, i32> = IdMap::new();
    /// assert!(map.is_empty());
    /// ```
    pub fn new() -> Self {
        IdMap {
            inner: IdVec::new(),
            num_present: I::Index::zero(),
        }
    }

    /// Constructs a new, empty `IdMap<I, T>` with the specified capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let map: IdMap<u32, i32> = IdMap::with_capacity(4);
    /// assert_eq!(map.capacity(), 4);
    /// ```
    pub fn with_capacity(mut capacity: usize) -> Self {
        capacity = capacity.min(I::Index::max_value().to_usize().unwrap_or(usize::MAX));
        let mut inner_vec = Vec::with_capacity(capacity);
        inner_vec.resize_with(capacity, || None);
        IdMap {
            inner: IdVec::from_vec(inner_vec),
            num_present: I::Index::zero(),
        }
    }

    /// Returns the number of entries in the `IdMap<I, T>`.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.num_present.to_usize_unchecked()
    }

    /// Returns `true` if the `IdMap<I, T>` contains no entries.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// assert!(map.is_empty());
    ///
    /// map.insert(5, "foo");
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.num_present.is_zero()
    }

    /// Inserts a key-value pair into the `IdMap<I, T>`.
    ///
    /// Returns the old value associated with the key if present, or `None` otherwise.
    ///
    /// # Complexity
    ///
    /// Let `max_key` refer to the largest key currently in the `IdMap<I, T>`:
    ///
    /// * If `id <= max_key`, runs in `O(1)` time.
    ///
    /// * If `id > max_key` but the `IdMap<I, T>` does not need to reallocate, runs in `O(id.to_index() - max_key.to_index())` time in the worst case.
    ///
    /// * If `id > max_key` and the `IdMap<I, T>` needs to reallocate, runs in `O(id.to_index())` time in the worst case.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// assert_eq!(map.get(5), Some(&"foo"));
    /// assert_eq!(map.get(10), Some(&"bar"));
    /// ```
    pub fn insert<J: Borrow<I>>(&mut self, id: J, value: T) -> Option<T> {
        let id = *id.borrow();
        let count_for_id = Count::from_last_id(id);
        let _ = self
            .inner
            .resize_with(count_for_id.max(self.inner.count()), || None);
        let existing = std::mem::replace(&mut self.inner[id], Some(value));
        if existing.is_none() {
            self.num_present = self.num_present + I::Index::one();
        }
        existing
    }

    /// Tries to insert a **new** key-value pair into the `IdMap<I, T>`, and returns a mutable
    /// reference to the inserted value.
    ///
    /// # Errors
    ///
    /// If the key is already present in the `IdMap<I, T>`, nothing is updated, and an error
    /// containing the provided `value` is returned.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let result = map.try_insert(10, "foo");
    /// assert!(result.is_ok());
    /// assert_eq!(map.get(10), Some(&"foo"));
    ///
    /// // 'try_insert' returns an error if the key is already present:
    /// let result = map.try_insert(10, "bar");
    /// assert!(result.is_err());
    /// // we can extract the value we tried to insert using 'into_value':
    /// assert_eq!(result.unwrap_err().into_value(), "bar");
    /// ```
    pub fn try_insert<J: Borrow<I>>(
        &mut self,
        id: J,
        value: T,
    ) -> Result<&mut T, OccupiedError<'_, I, T>> {
        let id = *id.borrow();
        let count_for_id = Count::from_last_id(id);
        let _ = self
            .inner
            .resize_with(count_for_id.max(self.inner.count()), || None);
        match &mut self.inner[id] {
            Some(_) => Err(OccupiedError::new(id, value)),
            entry @ None => {
                self.num_present = self.num_present + I::Index::one();
                Ok(entry.insert(value))
            }
        }
    }

    /// Inserts a **new** key-value pair into the `IdMap<I, T>`, and returns a mutable reference to
    /// the inserted value.
    ///
    /// # Panics
    ///
    /// Panics if the key is already present.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let foo_ref = map.insert_vacant(5, "foo");
    /// assert_eq!(*foo_ref, "foo");
    /// assert_eq!(map.get(5), Some(&"foo"));
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert_vacant(5, "foo");
    /// // cannot insert key '5' because the key is already present in the map:
    /// map.insert_vacant(5, "bar"); // panics!
    /// ```
    pub fn insert_vacant<J: Borrow<I>>(&mut self, id: J, value: T) -> &mut T {
        let id = *id.borrow();
        match self.try_insert(id, value) {
            Ok(new_ref) => new_ref,
            Err(err) => panic!("{err}"),
        }
    }

    /// Returns an [`Entry<I, T>`] for the given key in the `IdMap<I, T>`, for in-place
    /// manipulation.
    ///
    /// See the [`Entry<I, T>`] type for more details.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    ///
    /// // we can insert into vacant entries with 'or_insert':
    /// let value_ref = map.entry(5).or_insert("foo");
    /// assert_eq!(*value_ref, "foo");
    /// assert_eq!(map.get(5), Some(&"foo"));
    /// # assert_eq!(map.len(), 1);
    ///
    /// // calling 'or_insert' on an occupied entry has no effect:
    /// let value_ref = map.entry(5).or_insert("bar");
    /// assert_eq!(*value_ref, "foo");
    /// assert_eq!(map.get(5), Some(&"foo"));
    /// # assert_eq!(map.len(), 1);
    ///
    /// // we can modify an occupied entry with 'and_modify':
    /// map.entry(5).and_modify(|s| { *s = &s[1..]; });
    /// assert_eq!(map.get(5), Some(&"oo"));
    /// # assert_eq!(map.len(), 1);
    ///
    /// // calling 'and_modify' on a vacant entry has no effect:
    /// map.entry(10).and_modify(|s| { *s = &s[1..]; });
    /// assert!(map.get(10).is_none());
    /// # assert_eq!(map.len(), 1);
    /// ```
    pub fn entry<J: Borrow<I>>(&mut self, id: J) -> Entry<'_, I, T> {
        let id = *id.borrow();
        // NOTE: we need to index into 'self.inner' twice here, because if we were to e.g. directly
        // match on the return value of 'self.inner.get_mut(id)', then we would move 'self' during
        // the initial check such that 'self' would then be unavailable in the vacant case.
        if matches!(self.inner.get(id), Some(Some(_))) {
            Entry::Occupied(OccupiedEntry {
                id,
                num_present: &mut self.num_present,
                opt: &mut self.inner[id],
            })
        } else {
            Entry::Vacant(VacantEntry { id, map: self })
        }
    }

    /// Removes a key from the `IdMap<I, T>`. Returns the old value associated with the key, or
    /// `None` if the key was not present in the map.
    ///
    /// Calling `remove` leaves the capacity of the `IdMap<I, T>` unchanged.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// assert_eq!(map.get(5), Some(&"foo"));
    ///
    /// let removed = map.remove(5);
    /// assert_eq!(removed, Some("foo"));
    /// assert!(map.get(5).is_none());
    /// # assert!(map.is_empty());
    ///
    /// // removing a key which is not present in the map returns 'None':
    /// let removed = map.remove(100);
    /// assert!(removed.is_none());
    /// ```
    pub fn remove<J: Borrow<I>>(&mut self, id: J) -> Option<T> {
        let removed = self.inner.get_mut(id).and_then(|opt| opt.take());
        if removed.is_some() {
            self.num_present = self.num_present - I::Index::one();
        }
        removed
    }

    /// Removes all entries from the `IdMap<I, T>`.
    ///
    /// Calling `clear` leaves the capacity of the `IdMap<I, T>` unchanged.
    ///
    /// # Complexity:
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.inner.clear();
        self.num_present = I::Index::zero();
    }

    /// Removes all entries from the `IdMap<I, T>`, returning an iterator over their keys and
    /// values.
    ///
    /// The iterator is guaranteed to visit keys in ascending order.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// let iter = map.drain();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec![(5, "foo"), (10, "bar")]);
    /// assert!(map.is_empty());
    /// ```
    pub fn drain(&mut self) -> Drain<'_, I, T> {
        let num_present = self.num_present;
        self.num_present = I::Index::zero();
        Drain {
            num_present,
            inner: self.inner.drain_all(),
        }
    }

    /// Retains only the entries in the `IdMap<I, T>` for which `f` returns `true`.
    ///
    /// Calling `retain` leaves the capacity of the `IdMap<I, T>` unchanged.
    ///
    /// # Complexity
    ///
    /// Runs in `O(capacity)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "apple");
    /// map.insert(10, "pear");
    /// map.insert(15, "banana");
    /// map.insert(20, "lime");
    /// map.retain(|_, s| s.len() == 4);
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(map.get(5), None);
    /// assert_eq!(map.get(10), Some(&"pear"));
    /// assert_eq!(map.get(15), None);
    /// assert_eq!(map.get(20), Some(&"lime"));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(I, &mut T) -> bool,
    {
        for (id, opt) in &mut self.inner {
            if let Some(val) = opt {
                if !f(id, val) {
                    self.num_present = self.num_present - I::Index::one();
                    *opt = None;
                }
            }
        }
    }

    /// Returns `true` if the key is present in the `IdMap<I, T>`.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// assert!(map.contains_key(5));
    /// assert!(!map.contains_key(10));
    /// ```
    pub fn contains_key<J: Borrow<I>>(&self, id: J) -> bool {
        self.inner.get(id).map(Option::is_some).unwrap_or(false)
    }

    /// Returns a reference to the value corresponding to the key `id`, or `None` if the key is not
    /// present in the `IdMap<I, T>`.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(10, "foo");
    /// assert_eq!(map.get(10), Some(&"foo"));
    /// assert_eq!(map.get(20), None);
    /// ```
    pub fn get<J: Borrow<I>>(&self, id: J) -> Option<&T> {
        self.inner.get(id).and_then(|opt| opt.as_ref())
    }

    /// Returns a mutable reference to the value corresponding to the key `id`, or `None` if the key
    /// is not present in the `IdMap<I, T>`.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(10, "foo");
    /// assert!(map.get_mut(10).is_some());
    /// assert!(map.get_mut(20).is_none());
    ///
    /// *map.get_mut(10).unwrap() = "bar";
    /// assert_eq!(map.get(10), Some(&"bar"));
    /// ```
    pub fn get_mut<J: Borrow<I>>(&mut self, id: J) -> Option<&mut T> {
        self.inner.get_mut(id).and_then(|opt| opt.as_mut())
    }

    /// Returns simultaneous mutable reference to a pair of values in the `IdMap<I, T>` with
    /// distinct keys, or `None` if the keys are the same.
    ///
    /// # Panics
    ///
    /// Panics if either `id1` or `id2` is not present in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// let pair = map.get_pair_mut(5, 10);
    /// assert!(pair.is_some());
    /// let (foo_ref, bar_ref) = pair.unwrap();
    /// *foo_ref = "baz";
    /// *bar_ref = "biz";
    /// assert_eq!(map.get(5), Some(&"baz"));
    /// assert_eq!(map.get(10), Some(&"biz"));
    /// ```
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// // cannot get two simultaneous mutable reference to the same element:
    /// let pair = map.get_pair_mut(5, 5);
    /// assert!(pair.is_none());
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// // attempting to access a key which is not present in the map will panic:
    /// let pair = map.get_pair_mut(5, 10); // panics!
    /// ```
    pub fn get_pair_mut<J1: Borrow<I>, J2: Borrow<I>>(
        &mut self,
        id1: J1,
        id2: J2,
    ) -> Option<(&mut T, &mut T)> {
        let id1 = *id1.borrow();
        let id2 = *id2.borrow();
        self.inner.get_pair_mut(id1, id2).map(|pair| match pair {
            (Some(value1), Some(value2)) => (value1, value2),
            (None, _) => panic!(
                "key of type {} with index {} not present in IdMap",
                std::any::type_name::<I>(),
                id1.to_index()
            ),
            (_, None) => panic!(
                "key of type {} with index {} not present in IdMap",
                std::any::type_name::<I>(),
                id2.to_index()
            ),
        })
    }

    /// Returns an iterator over the keys and values of all entries in the `IdMap<I, T>`. The values
    /// are returned by immutable reference.
    ///
    /// The iterator is guaranteed to visit keys in ascending order.
    ///
    /// Calling `.iter()` is equivalent to calling `.into_iter()` on an `&IdMap<I, T>` reference.
    ///
    /// # Complexity
    ///
    /// Iterating over all elements using *forward iteration* (e.g. by calling
    /// [`next`](Iterator::next), or using a normal `for` loop) takes `O(max_key.to_index())` time,
    /// where `max_key` is the largest key in the `IdMap<I, T>`.
    ///
    /// Iterating over all elements using *backward iteration* (e.g. by calling
    /// [`next_back`](DoubleEndedIterator::next_back), or using the [`rev`](Iterator::rev) adaptor)
    /// takes `O(capacity)` time in the worst case.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// let iter = map.iter();
    /// # assert_eq!(iter.len(), 2);
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec![(5, &"foo"), (10, &"bar")]);
    /// ```
    pub fn iter(&self) -> Iter<'_, I, T> {
        Iter {
            num_present: self.num_present,
            inner: self.inner.iter(),
        }
    }

    /// Returns an iterator over the keys and values of all entries in the `IdMap<I, T>`. The values
    /// are returned by mutable reference.
    ///
    /// The iterator is guaranteed to visit keys in ascending order.
    ///
    /// Calling `.iter_mut()` is equivalent to calling `.into_iter()` on an `&mut IdMap<I, T>`
    /// reference.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// for (_, elem) in map.iter_mut() {
    ///     *elem = "baz";
    /// }
    /// assert_eq!(map.get(5), Some(&"baz"));
    /// assert_eq!(map.get(10), Some(&"baz"));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, I, T> {
        IterMut {
            num_present: self.num_present,
            inner: self.inner.iter_mut(),
        }
    }

    /// Returns an iterator over the keys of the `IdMap<I, T>`.
    ///
    /// The iterator is guaranteed to visit keys in ascending order.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// let iter = map.keys();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec![5, 10]);
    /// ```
    pub fn keys(&self) -> Keys<'_, I, T> {
        Keys { inner: self.iter() }
    }

    /// Returns an iterator over the values of the `IdMap<I, T>`. The values are returned by
    /// immutable reference.
    ///
    /// The iterator is guaranteed to visit entries in ascending order by key.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// let iter = map.values();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec![&"foo", &"bar"]);
    /// ```
    pub fn values(&self) -> Values<'_, I, T> {
        Values {
            num_present: self.num_present,
            inner: self.inner.values(),
        }
    }

    /// Returns an iterator over the values of the `IdMap<I, T>`. The values are returned by
    /// mutable reference.
    ///
    /// The iterator is guaranteed to visit entries in ascending order by key.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// for elem in map.values_mut() {
    ///     *elem = "baz";
    /// }
    /// assert_eq!(map.get(5), Some(&"baz"));
    /// assert_eq!(map.get(10), Some(&"baz"));
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, I, T> {
        ValuesMut {
            num_present: self.num_present,
            inner: self.inner.values_mut(),
        }
    }

    /// Returns an iterator over the values of the `IdMap<I, T>`. The values are moved out of the
    /// `IdMap<I, T>`.
    ///
    /// The iterator is guaranteed to visit entries in ascending order by key.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::iter`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.insert(10, "bar");
    /// let iter = map.into_values();
    /// let items = iter.collect::<Vec<_>>();
    /// assert_eq!(items, vec!["foo", "bar"]);
    /// ```
    pub fn into_values(self) -> IntoValues<I, T> {
        IntoValues {
            num_present: self.num_present,
            inner: self.inner.into_values(),
        }
    }

    /// Tries to convert the `IdMap<I, T>` into an [`IdVec<I, T>`] with the specified `count`.
    ///
    /// # Errors
    ///
    /// The keys of the `IdMap<I, T>` must correspond exactly to the range represented by `count`.
    /// If any keys less than `count` are absent from the `IdMap<I, T>`, or if any keys greater than
    /// or equal to `count` are present, an error is returned.
    ///
    /// # Complexity
    ///
    /// Runs in `O(max_key.to_index())` time, where `max_key` is the largest key in the `IdMap<I, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::{IdMap, Count};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(0, "foo");
    /// map.insert(1, "bar");
    /// map.insert(2, "baz");
    /// let result = map.try_to_id_vec(Count::from_value(3));
    /// assert!(result.is_ok());
    /// let vec = result.unwrap();
    /// assert_eq!(vec.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```
    /// # use id_collections::{IdMap, Count};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(0, "foo");
    /// map.insert(2, "bar");
    /// // map is missing key '1', so converting to an 'IdVec' with count '3' fails:
    /// let result = map.try_to_id_vec(Count::from_value(3));
    /// assert!(result.is_err());
    /// ```
    ///
    /// ```
    /// # use id_collections::{IdMap, Count};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(0, "foo");
    /// map.insert(1, "bar");
    /// map.insert(2, "baz");
    /// map.insert(10, "biz");
    /// // map has key '10', which is greater than the expected count of '3', so conversion fails:
    /// let result = map.try_to_id_vec(Count::from_value(3));
    /// assert!(result.is_err());
    /// ```
    pub fn try_to_id_vec(mut self, count: Count<I>) -> Result<IdVec<I, T>, TryToIdVecError<I, T>> {
        if self.num_present != count.to_value() {
            for (id, opt) in &self.inner {
                if count.contains(id) {
                    if opt.is_none() {
                        return Err(TryToIdVecError::absent(count, id));
                    }
                } else if opt.is_some() {
                    return Err(TryToIdVecError::present(count, id));
                }
            }
            unreachable!("'self.num_present' does not match contents of 'self.inner'");
        }

        self.inner.truncate(count);
        debug_assert!(self.inner.count() == count);

        self.inner.try_map(|id, opt| {
            #[allow(clippy::unnecessary_lazy_evaluations)]
            opt.ok_or_else(|| TryToIdVecError::absent(count, id))
        })
    }

    /// Converts the `IdMap<I, T>` into an [`IdVec<I, T>`] with the specified `count`.
    ///
    /// # Panics
    ///
    /// The keys of the `IdMap<I, T>` must correspond exactly to the range represented by `count`.
    /// If any keys less than `count` are absent from the `IdMap<I, T>`, or if any keys greater than
    /// or equal to `count` are present, the function panics.
    ///
    /// # Complexity
    ///
    /// Runs in `O(max_key)` time, where `max_key` is the largest key in the `IdMap<I, T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::{IdMap, Count};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(0, "foo");
    /// map.insert(1, "bar");
    /// map.insert(2, "baz");
    /// let vec = map.to_id_vec(Count::from_value(3));
    /// assert_eq!(vec.as_slice(), &["foo", "bar", "baz"]);
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::{IdMap, Count};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(0, "foo");
    /// map.insert(2, "bar");
    /// // map is missing key '1', so converting to an 'IdVec' with count '3' fails:
    /// let vec = map.to_id_vec(Count::from_value(3)); // panics!
    /// ```
    ///
    /// ```should_panic
    /// # use id_collections::{IdMap, Count};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(0, "foo");
    /// map.insert(1, "bar");
    /// map.insert(2, "baz");
    /// map.insert(10, "biz");
    /// // map has key '10', which is above than the expected count of '3', so conversion fails:
    /// let vec = map.to_id_vec(Count::from_value(3)); // panics!
    /// ```
    pub fn to_id_vec(self, count: Count<I>) -> IdVec<I, T> {
        match self.try_to_id_vec(count) {
            Ok(vec) => vec,
            Err(err) => panic!("{err}"),
        }
    }

    /// Returns the capacity of the `IdMap<I, T>`.
    ///
    /// Inserting a key whose index is less than the capacity is guaranteed to succeed without
    /// reallocating.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::with_capacity(4);
    /// assert_eq!(map.capacity(), 4);
    /// map.insert(2, "foo"); // guaranteed not to allocate
    /// ```
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Tries to increase capacity by at least `additional` entries. The `IdMap<I, T>` may reserve
    /// more than the requested capacity. After calling `try_reserve`, capacity will be greater than
    /// or equal to the value of `self.capacity() + additional` before the call.
    ///
    /// # Errors
    ///
    /// Returns an error if allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::with_capacity(8);
    /// match map.try_reserve(3) {
    ///     Ok(()) => assert!(map.capacity() >= 11),
    ///     Err(err) => eprintln!("allocation failed: {}", err),
    /// }
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        #[allow(clippy::unnecessary_lazy_evaluations)]
        self.inner
            .try_reserve(
                additional
                    .checked_add(self.inner.capacity() - self.inner.len())
                    .ok_or_else(|| TryReserveError { source: None })?,
            )
            .map_err(|err| TryReserveError { source: Some(err) })
    }

    /// Increases capacity by at least `additional` entries. The `IdMap<I, T>` may reserve more than
    /// the requested capacity. After calling `reserve`, capacity will be greater than or equal to
    /// the value of `self.capacity() + additional` before the call.
    ///
    /// # Panics
    ///
    /// Panics if allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::with_capacity(8);
    /// map.reserve(3);
    /// assert!(map.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(
            additional
                .checked_add(self.inner.capacity() - self.inner.len())
                .expect("cannot reserve additional capacity in IdMap: capacity overflows usize"),
        )
    }

    /// Shrinks the capacity of the `IdMap<I, T>` as much as possible.
    ///
    /// This will shrink down as close as possible to the largest key in the `IdMap<I, T>`, but
    /// some excess capacity may still be present depending on details of the implementation.
    ///
    /// # Complexity
    ///
    /// Runs in `O(capacity)` time in the worst case.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::with_capacity(100);
    /// map.insert(10, "foo");
    /// map.insert(20, "bar");
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 21);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        let last_present = self.inner.iter().rev().find(|(_, opt)| opt.is_some());
        let range = match last_present {
            Some((last_id, _)) => Count::from_last_id(last_id),
            None => Count::new(),
        };
        self.inner.truncate(range);
        self.inner.shrink_to_fit();
    }

    /// Shrinks the capacity of the `IdMap<I, T>` with a lower limit of `min_capacity`.
    ///
    /// Some capacity above `min_capacity` may still be present depending on details of the
    /// implementation.
    ///
    /// If the current capacity is less than `min_capacity`, this is a no-op.
    ///
    /// # Complexity
    ///
    /// Runs in `O(capacity)` time in the worst case.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::with_capacity(100);
    /// map.insert(10, "foo");
    /// map.insert(20, "bar");
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(50);
    /// assert!(map.capacity() >= 50);
    /// map.shrink_to(5);
    /// assert!(map.capacity() >= 21);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let last_present = self
            .inner
            .iter()
            .skip(min_capacity)
            .rev()
            .find(|(_, opt)| opt.is_some());
        let new_capacity = match last_present {
            Some((last_id, _)) => Count::from_last_id(last_id),
            None => Count::from_value(
                <I::Index as NumCast>::from(min_capacity).unwrap_or_else(I::Index::max_value),
            ),
        };
        self.inner.truncate(new_capacity);
        self.inner
            .shrink_to(new_capacity.to_value().to_usize().unwrap_or(usize::MAX));
    }

    // TODO: should we include 'remove_entry', for consistency with 'HashMap'?
}

impl<I: Id, T, J: Borrow<I>> Index<J> for IdMap<I, T> {
    type Output = T;

    fn index(&self, id: J) -> &Self::Output {
        let id = *id.borrow();
        match self.get(id) {
            Some(value) => value,
            None => match id.to_index().to_usize() {
                Some(id_value) => panic!("cannot index IdMap: key {id_value} not found"),
                None => panic!("cannot index IdMap: key not found"),
            },
        }
    }
}

impl<I: Id, T, J: Borrow<I>> Extend<(J, T)> for IdMap<I, T> {
    fn extend<It: IntoIterator<Item = (J, T)>>(&mut self, iter: It) {
        for (id, value) in iter {
            self.insert(id, value);
        }
    }
}

impl<'a, I: Id, T: Copy + 'a, J: Borrow<I>> Extend<(J, &'a T)> for IdMap<I, T> {
    fn extend<It: IntoIterator<Item = (J, &'a T)>>(&mut self, iter: It) {
        for (id, value) in iter {
            self.insert(id, *value);
        }
    }
}

impl<'a, I: Id, T, J: Borrow<I>> FromIterator<(J, T)> for IdMap<I, T> {
    fn from_iter<It: IntoIterator<Item = (J, T)>>(iter: It) -> Self {
        let mut result = IdMap::new();
        result.extend(iter);
        result
    }
}

impl<I: Id, T> From<IdVec<I, T>> for IdMap<I, T> {
    fn from(vec: IdVec<I, T>) -> Self {
        IdMap {
            num_present: vec.count().to_value(),
            inner: vec.map(|_, value| Some(value)),
        }
    }
}

/// An error indicating that an [`IdMap<I, T>`] could not be converted to an [`IdVec<I, T>`].
///
/// This error can be returned from [`IdMap::try_to_id_vec`]. See that function's documentation for
/// more details.
#[derive(Debug, Clone)]
pub struct TryToIdVecError<I: Id, T> {
    phantom: PhantomData<T>,
    count: Count<I>,
    kind: TryToIdVecErrorKind<I>,
}

#[derive(Debug, Clone)]
enum TryToIdVecErrorKind<I> {
    AbsentBeforeCount { id: I },
    PresentAfterCount { id: I },
}

impl<I: Id, T> TryToIdVecError<I, T> {
    fn absent(count: Count<I>, id: I) -> Self {
        TryToIdVecError {
            phantom: PhantomData,
            count,
            kind: TryToIdVecErrorKind::AbsentBeforeCount { id },
        }
    }

    fn present(count: Count<I>, id: I) -> Self {
        TryToIdVecError {
            phantom: PhantomData,
            count,
            kind: TryToIdVecErrorKind::PresentAfterCount { id },
        }
    }
}

impl<I: Id, T> Display for TryToIdVecError<I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.kind {
            TryToIdVecErrorKind::AbsentBeforeCount { id } => write!(
                f,
                "cannot convert IdMap to IdVec with count {}: key of type {} with index {} is \
                 absent",
                self.count.to_value(),
                std::any::type_name::<I>(),
                id.to_index()
            ),
            TryToIdVecErrorKind::PresentAfterCount { id } => write!(
                f,
                "cannot convert IdMap to IdVec with count {}: key of type {} with index {} exceeds \
                 bounds",
                self.count.to_value(),
                std::any::type_name::<I>(),
                id.to_index(),
            ),
        }
    }
}

impl<I: Id + Debug, T: Debug> std::error::Error for TryToIdVecError<I, T> {}

/// A view into a single entry in an `IdMap<I, T>`, which may be either vacant or occupied.
///
/// This type is returned from the [`IdMap::entry`] function.
#[derive(Debug)]
pub enum Entry<'a, I: Id, T> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, I, T>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, I, T>),
}

/// A view into an occupied entry in an `IdMap<I, T>`.
///
/// This type is part of the [`Entry<I, T>`] enum.
#[derive(Debug)]
pub struct OccupiedEntry<'a, I: Id, T> {
    id: I,
    num_present: &'a mut I::Index,
    opt: &'a mut Option<T>,
}

/// A view into a vacant entry in an `IdMap<I, T>`.
///
/// This type is part of the [`Entry<I, T>`] enum.
pub struct VacantEntry<'a, I: Id, T> {
    id: I,
    map: &'a mut IdMap<I, T>,
}

impl<'a, I: Id + Debug, T: Debug> Debug for VacantEntry<'a, I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // avoid generating extremely long debug output:
        f.debug_struct("VacantEntry").field("id", &self.id).finish()
    }
}

impl<'a, I: Id, T> Entry<'a, I, T> {
    /// Ensures a value is in the entry by inserting the provided `default` value if empty, and
    /// returns a mutable reference to the value in the entry.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let value_ref = map.entry(5).or_insert("foo");
    /// assert_eq!(*value_ref, "foo");
    /// *value_ref = "bar";
    /// assert_eq!(map.get(5), Some(&"bar"));
    ///
    /// // calling 'or_insert' on an occupied entry has no effect:
    /// let value_ref = map.entry(5).or_insert("baz");
    /// assert_eq!(*value_ref, "bar");
    /// ```
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Occupied(occupied) => occupied.opt.as_mut().unwrap(),
            Entry::Vacant(vacant) => vacant.map.insert_vacant(vacant.id, default),
        }
    }

    // TODO: should we include 'remove_entry' for consistency with 'Entry' for 'HashMap'?

    /// Ensures a value is in the entry by inserting the result of calling the `default` function if
    /// empty, and returns a mutable reference to the value in the entry.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let value_ref = map.entry(5).or_insert_with(|| "foo");
    /// assert_eq!(*value_ref, "foo");
    /// *value_ref = "bar";
    /// assert_eq!(map.get(5), Some(&"bar"));
    ///
    /// // calling 'or_insert_with' on an occupied entry has no effect:
    /// let value_ref = map.entry(5).or_insert_with(|| "baz");
    /// assert_eq!(*value_ref, "bar");
    /// ```
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(occupied) => occupied.opt.as_mut().unwrap(),
            Entry::Vacant(vacant) => vacant.map.insert_vacant(vacant.id, default()),
        }
    }

    /// Ensures a value is in the entry by inserting the result of calling the `default` function if
    /// empty, and returns a mutable reference to the value in the entry.
    ///
    /// Unlike [`Entry::or_insert_with`], this function passes the entry's key to the `default`
    /// function.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, String> = IdMap::new();
    /// let value_ref = map.entry(5).or_insert_with_key(|key| format!("default for key {key}"));
    /// assert_eq!(value_ref, "default for key 5");
    ///
    /// // calling 'or_insert_with' on an occupied entry has no effect:
    /// let value_ref = map.entry(5).or_insert_with_key(|_| "a different value".to_owned());
    /// assert_eq!(value_ref, "default for key 5");
    /// ```
    pub fn or_insert_with_key<F: FnOnce(I) -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Occupied(occupied) => occupied.opt.as_mut().unwrap(),
            Entry::Vacant(vacant) => vacant.map.insert_vacant(vacant.id, default(vacant.id)),
        }
    }

    /// Ensures a value is in the entry by inserting [`T::default`](Default::default) if empty, and
    /// returns a mutable reference to the value in the entry.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let value_ref = map.entry(5).or_default();
    /// assert_eq!(*value_ref, "");
    /// ```
    pub fn or_default(self) -> &'a mut T
    where
        T: Default,
    {
        self.or_insert_with(Default::default)
    }

    /// Returns the key for this entry.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let entry = map.entry(5);
    /// assert_eq!(entry.key(), 5);
    /// ```
    pub fn key(&self) -> I {
        match self {
            Entry::Occupied(occupied) => occupied.id,
            Entry::Vacant(vacant) => vacant.id,
        }
    }

    /// Modifies the value in the entry using the function `f`, if present.
    ///
    /// If the entry is vacant, this is a no-op.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// map.entry(5).and_modify(|s| { *s = &s[1..]; });
    /// assert_eq!(map.get(5), Some(&"oo"));
    ///
    /// // calling 'and_modify' on a vacant entry has no effect:
    /// map.entry(10).and_modify(|s| { *s = &s[1..]; });
    /// assert!(map.get(10).is_none());
    /// ```
    pub fn and_modify<F: FnOnce(&mut T)>(mut self, f: F) -> Self {
        if let Entry::Occupied(occupied) = &mut self {
            f(occupied.opt.as_mut().unwrap());
        }
        self
    }
}

impl<'a, I: Id, T> OccupiedEntry<'a, I, T> {
    /// Returns the key for this entry.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{id_map, IdMap};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Occupied(_)));
    /// if let id_map::Entry::Occupied(occupied) = entry {
    ///     assert_eq!(occupied.key(), 5);
    /// }
    /// ```
    pub fn key(&self) -> I {
        self.id
    }

    /// Returns a reference to the value for this entry.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{id_map, IdMap};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Occupied(_)));
    /// if let id_map::Entry::Occupied(occupied) = entry {
    ///     assert_eq!(occupied.get(), &"foo");
    /// }
    /// ```
    pub fn get(&self) -> &T {
        self.opt.as_ref().unwrap()
    }

    /// Returns a mutable reference to the value for this entry.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{id_map, IdMap};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Occupied(_)));
    /// if let id_map::Entry::Occupied(mut occupied) = entry {
    ///     *occupied.get_mut() = "bar";
    ///     assert_eq!(map.get(5), Some(&"bar"));
    /// }
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.opt.as_mut().unwrap()
    }

    /// Consumes the entry and returns a mutable reference to its value.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{id_map, IdMap};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Occupied(_)));
    /// if let id_map::Entry::Occupied(occupied) = entry {
    ///     *occupied.into_mut() = "bar";
    ///     assert_eq!(map.get(5), Some(&"bar"));
    /// }
    /// ```
    pub fn into_mut(self) -> &'a mut T {
        self.opt.as_mut().unwrap()
    }

    /// Replaces the value for this entry, returning the old value.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{id_map, IdMap};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Occupied(_)));
    /// if let id_map::Entry::Occupied(mut occupied) = entry {
    ///     let old = occupied.insert("bar");
    ///     assert_eq!(old, "foo");
    ///     assert_eq!(map.get(5), Some(&"bar"));
    /// }
    /// ```
    pub fn insert(&mut self, value: T) -> T {
        self.opt.replace(value).unwrap()
    }

    /// Removes this entry from the `IdMap<I, T>`, returning the old value.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{id_map, IdMap};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(5, "foo");
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Occupied(_)));
    /// if let id_map::Entry::Occupied(occupied) = entry {
    ///     let old = occupied.remove();
    ///     assert_eq!(old, "foo");
    ///     assert!(map.get(5).is_none());
    ///     # assert!(map.is_empty());
    /// }
    /// ```
    pub fn remove(self) -> T {
        *self.num_present = *self.num_present - I::Index::one();
        self.opt.take().unwrap()
    }
}

impl<'a, I: Id, T> VacantEntry<'a, I, T> {
    /// Returns the key for this entry.
    ///
    /// # Complexity
    ///
    /// Runs in `O(1)` time.
    ///
    /// # Example
    ///
    /// ```
    /// # use id_collections::{IdMap, id_map};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Vacant(_)));
    /// if let id_map::Entry::Vacant(vacant) = entry {
    ///     assert_eq!(vacant.key(), 5);
    /// }
    /// ```
    pub fn key(&self) -> I {
        self.id
    }

    /// Inserts a value into this entry, and returns a mutable reference to the new value.
    ///
    /// # Complexity
    ///
    /// The complexity is the same as [`IdMap::insert`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::{IdMap, id_map};
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// let entry = map.entry(5);
    /// assert!(matches!(entry, id_map::Entry::Vacant(_)));
    /// if let id_map::Entry::Vacant(vacant) = entry {
    ///     let value_ref = vacant.insert("foo");
    ///     assert_eq!(*value_ref, "foo");
    ///     *value_ref = "bar";
    ///     assert_eq!(map.get(5), Some(&"bar"));
    /// }
    /// ```
    pub fn insert(self, value: T) -> &'a mut T {
        self.map.insert_vacant(self.id, value)
    }
}

/// An error indicating that reserving additional capacity failed.
///
/// This error can be returned from [`IdMap::try_reserve`]. See that function's documentation for
/// more details.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TryReserveError {
    source: Option<std::collections::TryReserveError>,
}

impl Display for TryReserveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.source {
            Some(source) => Display::fmt(source, f),
            None => write!(f, "failed to reserve additional capacity for IdMap"),
        }
    }
}

impl std::error::Error for TryReserveError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.source {
            Some(source) => Some(source),
            None => None,
        }
    }
}

/// An error indicating that an entry in an [`IdMap<I, T>`] is already occupied.
///
/// This error can be returned from [`IdMap::try_insert`]. See that function's documentation for
/// more details.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccupiedError<'a, I: Id, T> {
    phantom: PhantomData<&'a mut T>,
    id: I,
    value: T,
}

impl<'a, I: Id, T> OccupiedError<'a, I, T> {
    fn new(id: I, value: T) -> Self {
        OccupiedError {
            phantom: PhantomData,
            id,
            value,
        }
    }

    /// Extracts the value which was to be inserted into the [`IdMap<I, T>`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use id_collections::IdMap;
    /// let mut map: IdMap<u32, &str> = IdMap::new();
    /// map.insert(10, "foo");
    /// // 'try_insert' returns an error if the key is already present:
    /// let result = map.try_insert(10, "bar");
    /// assert!(result.is_err());
    /// // we can extract the value we tried to insert using 'into_value':
    /// assert_eq!(result.unwrap_err().into_value(), "bar");
    /// ```
    pub fn into_value(self) -> T {
        self.value
    }
}

impl<'a, I: Id, T> Display for OccupiedError<'a, I, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "failed to insert into IdMap: key of type {} with index {} already exists",
            std::any::type_name::<I>(),
            self.id.to_index()
        )
    }
}

impl<'a, I: Id + Debug, T: Debug> std::error::Error for OccupiedError<'a, I, T> {}

macro_rules! impl_iter {
    (
        $(#[$attr:meta])*
        $name:ident { $($generic:tt)* } => $item_ty:ty
        where { $($bound:tt)* }
        { num_present: $num_present_ty:ty, inner: $inner_ty:ty, }
    ) => {
        $(#[$attr])*
        #[derive(Debug)]
        pub struct $name<$($generic)*> where $($bound)* {
            num_present: $num_present_ty,
            inner: $inner_ty,
        }

        impl<$($generic)*> Iterator for $name<$($generic)*> where $($bound)* {
            type Item = $item_ty;

            fn next(&mut self) -> Option<Self::Item> {
                // optimization to avoid processing vacant entries
                if self.num_present.is_zero() {
                    return None;
                }
                for (id, opt) in self.inner.by_ref() {
                    if let Some(value) = opt {
                        self.num_present = self.num_present - <$num_present_ty>::one();
                        return Some((id, value));
                    }
                }
                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (
                    self.num_present.to_usize_unchecked(),
                    Some(self.num_present.to_usize_unchecked()),
                )
            }

            fn count(self) -> usize {
                self.num_present.to_usize_unchecked()
            }

            fn last(mut self) -> Option<Self::Item> {
                self.next_back()
            }
        }

        impl<$($generic)*> DoubleEndedIterator for $name<$($generic)*> where $($bound)* {
            fn next_back(&mut self) -> Option<Self::Item> {
                // optimization to avoid processing vacant entries:
                if self.num_present.is_zero() {
                    return None;
                }
                while let Some((id, opt)) = self.inner.next_back() {
                    if let Some(value) = opt {
                        self.num_present = self.num_present - <$num_present_ty>::one();
                        return Some((id, value));
                    }
                }
                None
            }
        }

        impl<$($generic)*> ExactSizeIterator for $name<$($generic)*> where $($bound)* {
            fn len(&self) -> usize {
                self.num_present.to_usize_unchecked()
            }
        }

        impl<$($generic)*> FusedIterator for $name<$($generic)*> where $($bound)* {}
    }
}

impl_iter! {
    /// An iterator over the entries of an [`IdMap<I, T>`] which returns values by immutable
    /// reference.
    ///
    /// This type is returned by [`IdMap::iter`]. See that function's documentation for more
    /// details.
    Iter { 'a, I, T } => (I, &'a T) where { I: Id } {
        num_present: I::Index,
        inner: id_vec::Iter<'a, I, Option<T>>,
    }
}

impl_iter! {
    /// An iterator over the entries of an [`IdMap<I, T>`] which returns values by mutable
    /// reference.
    ///
    /// This type is returned by [`IdMap::iter_mut`]. See that function's documentation for more
    /// details.
    IterMut { 'a, I, T } => (I, &'a mut T) where { I: Id } {
        num_present: I::Index,
        inner: id_vec::IterMut<'a, I, Option<T>>,
    }
}

impl_iter! {
    /// An iterator over the entries of an [`IdMap<I, T>`] which returns values by move.
    ///
    /// This type is returned by [`IdMap::into_iter`](struct.IdMap.html#impl-IntoIterator-2). See
    /// that function's documentation for more details.
    IntoIter { I, T } => (I, T) where { I: Id } {
        num_present: I::Index,
        inner: id_vec::IntoIter<I, Option<T>>,
    }
}

impl_iter! {
    /// A draining iterator for [`IdMap<I, T>`].
    ///
    /// This type is returned by [`IdMap::drain`]. See that function's documentation for more
    /// details.
    Drain { 'a, I, T } => (I, T) where { I: Id } {
        num_present: I::Index,
        inner: id_vec::Drain<'a, I, Option<T>>,
    }
}

impl<'a, I: Id, T> IntoIterator for &'a IdMap<I, T> {
    type Item = (I, &'a T);
    type IntoIter = Iter<'a, I, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, I: Id, T> IntoIterator for &'a mut IdMap<I, T> {
    type Item = (I, &'a mut T);
    type IntoIter = IterMut<'a, I, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<I: Id, T> IntoIterator for IdMap<I, T> {
    type Item = (I, T);
    type IntoIter = IntoIter<I, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            num_present: self.num_present,
            inner: self.inner.into_iter(),
        }
    }
}

#[cfg(test)]
mod entries_iter_test {
    use crate::IdMap;

    #[test]
    fn test_size_hint() {
        let map = IdMap::<u32, _>::from_iter([(1, "x"), (3, "y"), (5, "z")]);
        assert_eq!(map.iter().size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_count() {
        let map = IdMap::<u32, _>::from_iter([(1, "x"), (3, "y"), (5, "z")]);
        assert_eq!(map.iter().count(), 3);
    }

    #[test]
    fn test_last() {
        let map = IdMap::<u32, _>::from_iter([(1, "x"), (3, "y"), (5, "z")]);
        assert_eq!(map.iter().last(), Some((5, &"z")));
    }

    #[test]
    fn test_next_back() {
        let mut map = IdMap::<u32, _>::with_capacity(10);
        map.extend([(1, "x"), (3, "y"), (5, "z")]);
        let mut it = map.iter();
        assert_eq!(it.next_back(), Some((5, &"z")));
        assert_eq!(it.len(), 2);
        assert_eq!(it.next(), Some((1, &"x")));
        assert_eq!(it.len(), 1);
        assert_eq!(it.next(), Some((3, &"y")));
        assert_eq!(it.len(), 0);
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
        assert_eq!(it.len(), 0);
    }
}

/// An iterator over the keys of an [`IdMap<I, T>`].
///
/// This type is returned from [`IdMap::keys`]. See that function's documentation for more details.
#[derive(Debug)]
pub struct Keys<'a, I: Id, T> {
    inner: Iter<'a, I, T>,
}

impl<'a, I: Id, T> Iterator for Keys<'a, I, T> {
    type Item = I;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(id, _)| id)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }

    fn count(self) -> usize {
        self.inner.count()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, I: Id, T> DoubleEndedIterator for Keys<'a, I, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(id, _)| id)
    }
}

impl<'a, I: Id, T> ExactSizeIterator for Keys<'a, I, T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a, I: Id, T> FusedIterator for Keys<'a, I, T> {}

macro_rules! impl_values_iter {
    (
        $(#[$attr:meta])*
        $name:ident { $($generic:tt)* } => $item_ty:ty
        where { $($bound:tt)* }
        { num_present: $num_present_ty:ty, inner: $inner_ty:ty, }
    ) => {
        $(#[$attr])*
        #[derive(Debug)]
        pub struct $name<$($generic)*> where $($bound)* {
            num_present: $num_present_ty,
            inner: $inner_ty,
        }

        impl<$($generic)*> Iterator for $name<$($generic)*> where $($bound)* {
            type Item = $item_ty;

            fn next(&mut self) -> Option<Self::Item> {
                // optimization to avoid processing vacant entries
                if self.num_present.is_zero() {
                    return None;
                }
                for opt in self.inner.by_ref() {
                    if let Some(value) = opt {
                        self.num_present = self.num_present - <$num_present_ty>::one();
                        return Some(value);
                    }
                }
                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (
                    self.num_present.to_usize_unchecked(),
                    Some(self.num_present.to_usize_unchecked()),
                )
            }

            fn count(self) -> usize {
                self.num_present.to_usize_unchecked()
            }

            fn last(mut self) -> Option<Self::Item> {
                self.next_back()
            }
        }

        impl<$($generic)*> DoubleEndedIterator for $name<$($generic)*> where $($bound)* {
            fn next_back(&mut self) -> Option<Self::Item> {
                // optimization to avoid processing vacant entries:
                if self.num_present.is_zero() {
                    return None;
                }
                while let Some(opt) = self.inner.next_back() {
                    if let Some(value) = opt {
                        self.num_present = self.num_present - <$num_present_ty>::one();
                        return Some(value);
                    }
                }
                None
            }
        }

        impl<$($generic)*> ExactSizeIterator for $name<$($generic)*> where $($bound)* {
            fn len(&self) -> usize {
                self.num_present.to_usize_unchecked()
            }
        }

        impl<$($generic)*> FusedIterator for $name<$($generic)*> where $($bound)* {}
    }
}

impl_values_iter! {
    /// An iterator over the values of an [`IdMap<I, T>`] which returns values by immutable
    /// reference.
    ///
    /// This type is returned from [`IdMap::values`]. See that function's documentation for more
    /// details.
    Values { 'a, I, T } => &'a T where { I: Id } {
        num_present: I::Index,
        inner: std::slice::Iter<'a, Option<T>>,
    }
}

impl_values_iter! {
    /// An iterator over the values of an [`IdMap<I, T>`] which returns values by mutable reference.
    ///
    /// This type is returned from [`IdMap::values_mut`]. See that function's documentation for more details.
    ValuesMut { 'a, I, T } => &'a mut T where { I: Id } {
        num_present: I::Index,
        inner: std::slice::IterMut<'a, Option<T>>,
    }
}

impl_values_iter! {
    /// An iterator over the values of an [`IdMap<I, T>`] which returns values by move.
    ///
    /// This type is returned from [`IdMap::into_values`]. See that function's documentation for more details.
    IntoValues { I, T } => T where { I: Id } {
        num_present: I::Index,
        inner: std::vec::IntoIter<Option<T>>,
    }
}

#[cfg(test)]
mod values_iter_test {
    use crate::IdMap;

    #[test]
    fn test_size_hint() {
        let map = IdMap::<u32, _>::from_iter([(1, "x"), (3, "y"), (5, "z")]);
        assert_eq!(map.values().size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_count() {
        let map = IdMap::<u32, _>::from_iter([(1, "x"), (3, "y"), (5, "z")]);
        assert_eq!(map.values().count(), 3);
    }

    #[test]
    fn test_last() {
        let map = IdMap::<u32, _>::from_iter([(1, "x"), (3, "y"), (5, "z")]);
        assert_eq!(map.values().last(), Some(&"z"));
    }

    #[test]
    fn test_next_back() {
        let mut map = IdMap::<u32, _>::with_capacity(10);
        map.extend([(1, "x"), (3, "y"), (5, "z")]);
        let mut it = map.values();
        assert_eq!(it.next_back(), Some(&"z"));
        assert_eq!(it.len(), 2);
        assert_eq!(it.next(), Some(&"x"));
        assert_eq!(it.len(), 1);
        assert_eq!(it.next(), Some(&"y"));
        assert_eq!(it.len(), 0);
        assert_eq!(it.next(), None);
        assert_eq!(it.next_back(), None);
        assert_eq!(it.len(), 0);
    }
}
