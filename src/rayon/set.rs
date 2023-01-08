use std::hash::{BuildHasher, Hash};

use super::{collect, map};
use crate::FlatMultiset;
use rayon::iter::plumbing::UnindexedConsumer;
use rayon::iter::{FromParallelIterator, IntoParallelIterator, ParallelExtend, ParallelIterator};

/// Parallel iterator over elements of a consumed set.
pub struct IntoParIter<T> {
    inner: map::IntoParIter<T, ()>,
}

impl<T: Send> ParallelIterator for IntoParIter<T> {
    type Item = T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner.map(|(k, _)| k).drive_unindexed(consumer)
    }
}

/// Parallel iterator over shared references to elements in a set.
pub struct ParIter<'a, T> {
    inner: map::ParKeys<'a, T, ()>,
}

impl<'a, T: Sync> ParallelIterator for ParIter<'a, T> {
    type Item = &'a T;

    fn drive_unindexed<C>(self, consumer: C) -> C::Result
    where
        C: UnindexedConsumer<Self::Item>,
    {
        self.inner.drive_unindexed(consumer)
    }
}

impl<T: Send, S> IntoParallelIterator for FlatMultiset<T, S> {
    type Item = T;
    type Iter = IntoParIter<T>;

    fn into_par_iter(self) -> Self::Iter {
        IntoParIter {
            inner: self.map.into_par_iter(),
        }
    }
}

impl<'a, T: Sync, S> IntoParallelIterator for &'a FlatMultiset<T, S> {
    type Item = &'a T;
    type Iter = ParIter<'a, T>;

    fn into_par_iter(self) -> Self::Iter {
        ParIter {
            inner: self.map.par_keys(),
        }
    }
}

impl<T, S> FromParallelIterator<T> for FlatMultiset<T, S>
where
    T: Eq + Hash + Send,
    S: BuildHasher + Default,
{
    fn from_par_iter<P>(par_iter: P) -> Self
    where
        P: IntoParallelIterator<Item = T>,
    {
        let mut set = FlatMultiset::default();
        set.par_extend(par_iter);
        set
    }
}

impl<T, S> ParallelExtend<T> for FlatMultiset<T, S>
where
    T: Eq + Hash + Send,
    S: BuildHasher,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = T>,
    {
        extend(self, par_iter);
    }
}

impl<'a, T, S> ParallelExtend<&'a T> for FlatMultiset<T, S>
where
    T: 'a + Copy + Eq + Hash + Sync,
    S: BuildHasher,
{
    fn par_extend<I>(&mut self, par_iter: I)
    where
        I: IntoParallelIterator<Item = &'a T>,
    {
        extend(self, par_iter);
    }
}

fn extend<T, S, I>(set: &mut FlatMultiset<T, S>, par_iter: I)
where
    T: Eq + Hash,
    S: BuildHasher,
    I: IntoParallelIterator,
    FlatMultiset<T, S>: Extend<I::Item>,
{
    let (list, len) = collect(par_iter);

    set.reserve(len);

    for vec in list {
        set.extend(vec);
    }
}
