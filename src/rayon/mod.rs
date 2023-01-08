/// Parallel iterator types for `FlatMultimap` with [rayon](https://docs.rs/rayon/latest/rayon/).
pub mod map;

/// Parallel iterator types for `FlatMultiset` with [rayon](https://docs.rs/rayon/latest/rayon/).
pub mod set;

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use std::collections::LinkedList;

#[allow(clippy::linkedlist)]
pub fn collect<I: IntoParallelIterator>(iter: I) -> (LinkedList<Vec<I::Item>>, usize) {
    let list = iter
        .into_par_iter()
        .fold(Vec::new, |mut vec, elem| {
            vec.push(elem);
            vec
        })
        .map(|vec| {
            let mut list = LinkedList::new();
            list.push_back(vec);
            list
        })
        .reduce(LinkedList::new, |mut list1, mut list2| {
            list1.append(&mut list2);
            list1
        });

    let len = list.iter().map(Vec::len).sum();

    (list, len)
}
