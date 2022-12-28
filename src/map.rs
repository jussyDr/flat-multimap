use hashbrown::raw::{RawIter, RawTable};
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
