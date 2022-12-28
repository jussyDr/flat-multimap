use hashbrown::raw::{RawIntoIter, RawIter, RawTable};
use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};
use std::marker::PhantomData;

/// Multimap implementation where entries are stored as a flattened hash map.
///
/// # Examples
///
/// ```
/// use flat_multimap::FlatMultimap;
///
/// let mut map = FlatMultimap::new();
/// map.insert(1, 1);
/// map.insert(1, 2);
/// map.insert(2, 3);
///
/// assert_eq!(map.len(), 3);
/// ```
#[derive(Default)]
pub struct FlatMultimap<K, V, S = RandomState> {
    hash_builder: S,
    table: RawTable<(K, V)>,
}

impl<K, V> FlatMultimap<K, V, RandomState> {
    /// Creates an empty `FlatMultimap` with a capacity of 0.
    #[must_use]
    pub fn new() -> Self {
        Self::with_hasher(RandomState::default())
    }

    /// Creates an empty `FlatMultimap` with at least the specified capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, RandomState::default())
    }
}

impl<K, V, S> FlatMultimap<K, V, S> {
    /// Creates an empty `FlatMultimap` with default capacity which will use the given hash builder to hash keys.
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::new(),
        }
    }

    /// Creates an empty `FlatMultimap` with at least the specified capacity, using the given hash builder to hash keys.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            table: RawTable::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.table.capacity()
    }

    /// Returns a reference to the map’s [`BuildHasher`].    
    pub const fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements in the map.
    pub fn len(&self) -> usize {
        self.table.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory for reuse.
    pub fn clear(&mut self) {
        self.table.clear();
    }

    /// An iterator visiting all key-value pairs in arbitrary order. The iterator element type is `(&'a K, &'a V)`.
    pub fn iter(&self) -> Iter<'_, K, V> {
        unsafe {
            Iter {
                iter: self.table.iter(),
                phantom: PhantomData,
            }
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with mutable references to the values.
    /// The iterator element type is (&'a K, &'a mut V).
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        unsafe {
            IterMut {
                iter: self.table.iter(),
                phantom: PhantomData,
            }
        }
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use flat_multimap::FlatMultimap;
    ///
    /// let mut map = FlatMultimap::new();
    /// map.insert(1, 1);
    /// map.insert(1, 2);
    /// map.insert(2, 3);
    ///
    /// let mut keys: Vec<_> = map.keys().collect();
    /// keys.sort_unstable(); // Sort since the keys are visited in arbitrary order.
    ///
    /// assert_eq!(keys, [&1, &1, &2]);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { iter: self.iter() }
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type is `K`.
    pub fn into_keys(self) -> IntoKeys<K, V> {
        IntoKeys {
            iter: self.into_iter(),
        }
    }

    /// An iterator visiting all values in arbitrary order. The iterator element type is `&'a V`.
    pub fn values(&self) -> Values<'_, K, V> {
        Values { iter: self.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order. The iterator element type is `&'a mut V`.
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            iter: self.iter_mut(),
        }
    }

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The map cannot be used after calling this. The iterator element type is `V`.
    pub fn into_values(self) -> IntoValues<K, V> {
        IntoValues {
            iter: self.into_iter(),
        }
    }
}

impl<K, V, S> FlatMultimap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /// Inserts a key-value pair into the map.
    pub fn insert(&mut self, key: K, value: V) {
        let hash = make_hash(&self.hash_builder, &key);

        self.table
            .insert(hash, (key, value), |x| make_hash(&self.hash_builder, &x.0));
    }

    /// Removes an arbitrary value with the given key from the map, returning the removed value if there was a value at the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use flat_multimap::FlatMultimap;
    ///
    /// let mut map = FlatMultimap::new();
    /// map.insert(1, 1);
    /// map.insert(1, 2);
    ///
    /// assert!(map.remove(&1).is_some()); // Could be either Some(1) or Some(2).
    /// assert!(map.remove(&1).is_some()); // Could be either Some(1) or Some(2).
    /// assert!(map.remove(&1).is_none());
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let hash = make_hash(&self.hash_builder, key);

        self.table
            .remove_entry(hash, equivalent_key(key))
            .map(|(_, value)| value)
    }

    /// Returns `true` if the map contains at least a single value for the specified key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        let hash = make_hash(&self.hash_builder, key);

        self.table.find(hash, equivalent_key(key)).is_some()
    }
}

impl<'a, K, V, S> IntoIterator for &'a FlatMultimap<K, V, S> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K, V, S> IntoIterator for &'a mut FlatMultimap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

impl<K, V, S> IntoIterator for FlatMultimap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            iter: self.table.into_iter(),
        }
    }
}

/// An iterator over the entries of a `FlatMultimap`.
pub struct Iter<'a, K, V> {
    iter: RawIter<(K, V)>,
    phantom: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        self.iter.next().map(|bucket| unsafe {
            let bucket = bucket.as_ref();
            (&bucket.0, &bucket.1)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A mutable iterator over the entries of a `FlatMultimap`.
pub struct IterMut<'a, K, V> {
    iter: RawIter<(K, V)>,
    phantom: PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        self.iter.next().map(|bucket| unsafe {
            let bucket = bucket.as_mut();
            (&bucket.0, &mut bucket.1)
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An owning iterator over the entries of a `FlatMultimap`.
pub struct IntoIter<K, V> {
    iter: RawIntoIter<(K, V)>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An iterator over the keys of a `FlatMultimap`.
pub struct Keys<'a, K, V> {
    iter: Iter<'a, K, V>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        self.iter.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An owning iterator over the keys of a `FlatMultimap`.
pub struct IntoKeys<K, V> {
    iter: IntoIter<K, V>,
}

impl<K, V> Iterator for IntoKeys<K, V> {
    type Item = K;

    fn next(&mut self) -> Option<K> {
        self.iter.next().map(|(key, _)| key)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An iterator over the values of a `FlatMultimap`.
pub struct Values<'a, K, V> {
    iter: Iter<'a, K, V>,
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> {
        self.iter.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A mutable iterator over the values of a `FlatMultimap`.
pub struct ValuesMut<'a, K, V> {
    iter: IterMut<'a, K, V>,
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<&'a mut V> {
        self.iter.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An owning iterator over the values of a `FlatMultimap`.
pub struct IntoValues<K, V> {
    iter: IntoIter<K, V>,
}

impl<K, V> Iterator for IntoValues<K, V> {
    type Item = V;

    fn next(&mut self) -> Option<V> {
        self.iter.next().map(|(_, value)| value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

fn equivalent_key<Q, K, V>(k: &Q) -> impl Fn(&(K, V)) -> bool + '_
where
    K: Borrow<Q>,
    Q: ?Sized + Hash + Eq,
{
    move |x| k == x.0.borrow()
}

fn make_hash<T, S>(hash_builder: &S, value: &T) -> u64
where
    T: ?Sized + Hash,
    S: BuildHasher,
{
    let mut state = hash_builder.build_hasher();
    value.hash(&mut state);
    state.finish()
}
