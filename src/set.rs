use crate::map::{FlatMultimap, IntoKeys, Keys};
use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt::{self, Debug};
use std::hash::{BuildHasher, Hash};
use std::iter::FusedIterator;

/// Multiset implementation where items are stored as a flattened hash set.
///
/// # Examples
///
/// ```
/// use flat_multimap::FlatMultiset;
///
/// let mut set = FlatMultiset::new();
/// set.insert(1);
/// set.insert(1);
/// set.insert(2);
///
/// assert_eq!(set.len(), 3);
/// ```
#[derive(Clone, Default)]
pub struct FlatMultiset<T, S = RandomState> {
    map: FlatMultimap<T, (), S>,
}

impl<T> FlatMultiset<T, RandomState> {
    /// Creates an empty `FlatMultiset` with a capacity of 0.
    #[must_use]
    pub fn new() -> Self {
        Self {
            map: FlatMultimap::new(),
        }
    }

    /// Creates an empty `FlatMultiset` with at least the specified capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: FlatMultimap::with_capacity(capacity),
        }
    }
}

impl<T, S> FlatMultiset<T, S> {
    /// Creates an empty `FlatMultiset` with default capacity which will use the given hash builder to hash keys.
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            map: FlatMultimap::with_hasher(hash_builder),
        }
    }

    /// Creates an empty `FlatMultiset` with at least the specified capacity, using the given hash builder to hash keys.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            map: FlatMultimap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Returns a reference to the set's [`BuildHasher`].
    pub const fn hasher(&self) -> &S {
        self.map.hasher()
    }

    /// Returns the number of elements in the set.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the set contains no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the set, removing all values.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// An iterator visiting all elements in arbitrary order. The iterator element type is `&'a T`.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.map.keys(),
        }
    }
}

impl<T, S> FlatMultiset<T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    /// Adds a value to the set.
    pub fn insert(&mut self, value: T) {
        self.map.insert(value, ());
    }

    /// Removes a value from the set. Returns whether the value was present in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use flat_multimap::FlatMultiset;
    ///
    /// let mut set = FlatMultiset::new();
    /// set.insert(1);
    /// set.insert(1);
    ///
    /// assert!(set.remove(&1));
    /// assert!(set.remove(&1));
    /// assert!(!set.remove(&1));
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.map.remove(value).is_some()
    }

    /// Returns `true` if the set contains the value.
    pub fn contains<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.map.contains_key(value)
    }
}

impl<'a, T, S> IntoIterator for &'a FlatMultiset<T, S> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T, S> IntoIterator for FlatMultiset<T, S> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            iter: self.map.into_keys(),
        }
    }
}

impl<T, S> Debug for FlatMultiset<T, S>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// An iterator over the items of a `FlatMultiset`.
pub struct Iter<'a, T> {
    iter: Keys<'a, T, ()>,
}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

impl<T: Debug> Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An owning iterator over the items of a `FlatMultiset`.
pub struct IntoIter<T> {
    iter: IntoKeys<T, ()>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for IntoIter<T> {}

impl<T: Debug> Debug for IntoIter<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter.iter()).finish()
    }
}
