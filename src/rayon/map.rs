use super::collect;
use crate::FlatMultimap;
use hashbrown::raw::rayon::{RawIntoParIter, RawParIter};
use rayon::iter::plumbing::UnindexedConsumer;
use rayon::iter::{FromParallelIterator, IntoParallelIterator, ParallelExtend, ParallelIterator};
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;

/// Parallel iterator over shared references to entries in a map.
#[derive(Clone)]
pub struct ParIter<'a, K, V> {
    inner: RawParIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K: Sync, V: Sync> ParallelIterator for ParIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<(&'a K, &'a V)>,
    {
        self.inner
            .map(|x| unsafe {
                let r = x.as_ref();
                (&r.0, &r.1)
            })
            .drive_unindexed(consumer)
    }
}

/// Parallel iterator over shared references to keys in a map.
#[derive(Clone)]
pub struct ParKeys<'a, K, V> {
    inner: RawParIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K: Sync, V: Sync> ParallelIterator for ParKeys<'a, K, V> {
    type Item = &'a K;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner
            .map(|x| unsafe { &x.as_ref().0 })
            .drive_unindexed(consumer)
    }
}

/// Parallel iterator over shared references to values in a map.
#[derive(Clone)]
pub struct ParValues<'a, K, V> {
    inner: RawParIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a V)>,
}

impl<'a, K: Sync, V: Sync> ParallelIterator for ParValues<'a, K, V> {
    type Item = &'a V;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner
            .map(|x| unsafe { &x.as_ref().1 })
            .drive_unindexed(consumer)
    }
}

/// Parallel iterator over mutable references to entries in a map.
pub struct ParIterMut<'a, K, V> {
    inner: RawParIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, K: Sync, V: Send> ParallelIterator for ParIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner
            .map(|x| unsafe {
                let r = x.as_mut();
                (&r.0, &mut r.1)
            })
            .drive_unindexed(consumer)
    }
}

/// Parallel iterator over mutable references to values in a map.
pub struct ParValuesMut<'a, K, V> {
    inner: RawParIter<(K, V)>,
    marker: PhantomData<(&'a K, &'a mut V)>,
}

impl<'a, K: Sync, V: Send> ParallelIterator for ParValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner
            .map(|x| unsafe { &mut x.as_mut().1 })
            .drive_unindexed(consumer)
    }
}

/// Parallel iterator over entries of a consumed map.
pub struct IntoParIter<K, V> {
    inner: RawIntoParIter<(K, V)>,
}

impl<K: Send, V: Send> ParallelIterator for IntoParIter<K, V> {
    type Item = (K, V);

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner.drive_unindexed(consumer)
    }
}

impl<K: Sync, V: Sync, S> FlatMultimap<K, V, S> {
    /// Visits (potentially in parallel) immutably borrowed keys in an arbitrary order.
    pub fn par_keys(&self) -> ParKeys<'_, K, V> {
        ParKeys {
            inner: unsafe { self.table.par_iter() },
            marker: PhantomData,
        }
    }

    /// Visits (potentially in parallel) immutably borrowed values in an arbitrary order.
    pub fn par_values(&self) -> ParValues<'_, K, V> {
        ParValues {
            inner: unsafe { self.table.par_iter() },
            marker: PhantomData,
        }
    }
}

impl<K: Send, V: Send, S> FlatMultimap<K, V, S> {
    /// Visits (potentially in parallel) mutably borrowed values in an arbitrary order.
    pub fn par_values_mut(&mut self) -> ParValuesMut<'_, K, V> {
        ParValuesMut {
            inner: unsafe { self.table.par_iter() },
            marker: PhantomData,
        }
    }
}

impl<K: Send, V: Send, S> IntoParallelIterator for FlatMultimap<K, V, S> {
    type Item = (K, V);
    type Iter = IntoParIter<K, V>;

    fn into_par_iter(self) -> Self::Iter {
        IntoParIter {
            inner: self.table.into_par_iter(),
        }
    }
}

impl<'a, K: Sync, V: Sync, S> IntoParallelIterator for &'a FlatMultimap<K, V, S> {
    type Item = (&'a K, &'a V);
    type Iter = ParIter<'a, K, V>;

    fn into_par_iter(self) -> Self::Iter {
        ParIter {
            inner: unsafe { self.table.par_iter() },
            marker: PhantomData,
        }
    }
}

impl<'a, K: Sync, V: Send, S> IntoParallelIterator for &'a mut FlatMultimap<K, V, S> {
    type Item = (&'a K, &'a mut V);
    type Iter = ParIterMut<'a, K, V>;

    fn into_par_iter(self) -> Self::Iter {
        ParIterMut {
            inner: unsafe { self.table.par_iter() },
            marker: PhantomData,
        }
    }
}

impl<K, V, S> FromParallelIterator<(K, V)> for FlatMultimap<K, V, S>
where
    K: Eq + Hash + Send,
    V: Send,
    S: BuildHasher + Default,
{
    fn from_par_iter<P>(par_iter: P) -> Self
    where
        P: IntoParallelIterator<Item = (K, V)>,
    {
        let mut map = FlatMultimap::default();
        map.par_extend(par_iter);
        map
    }
}

impl<K, V, S> ParallelExtend<(K, V)> for FlatMultimap<K, V, S>
where
    K: Eq + Hash + Send,
    V: Send,
    S: BuildHasher,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = (K, V)>,
    {
        extend(self, par_iter);
    }
}

impl<'a, K, V, S> ParallelExtend<(&'a K, &'a V)> for FlatMultimap<K, V, S>
where
    K: Copy + Eq + Hash + Sync,
    V: Copy + Sync,
    S: BuildHasher,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = (&'a K, &'a V)>,
    {
        extend(self, par_iter);
    }
}

fn extend<K, V, S, I>(map: &mut FlatMultimap<K, V, S>, par_iter: I)
where
    K: Eq + Hash,
    S: BuildHasher,
    I: IntoParallelIterator,
    FlatMultimap<K, V, S>: Extend<I::Item>,
{
    let (list, len) = collect(par_iter);

    map.reserve(len);

    for vec in list {
        map.extend(vec);
    }
}
