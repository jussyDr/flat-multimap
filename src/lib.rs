//! A multimap and multiset implementation using a flattened hash table.
//!
//! ---
//!
//! [`FlatMultimap`] is a [multimap](https://en.wikipedia.org/wiki/Multimap)
//! implementation where entries are stored as a flattened hash map:
//!  - `a -> 1`
//!  - `a -> 2`
//!  - `b -> 3`
//!
//! as opposed to the common implementation using a hash map
//! which maps keys to a collection of values:
//!  - `a -> 1, 2`
//!  - `b -> 3`
//!
//! ---
//!
//! [`FlatMultiset`] is a [multiset](https://en.wikipedia.org/wiki/Multiset)
//! implementation where items are stored as a flattened hash set:
//!  - `a`
//!  - `a`
//!  - `b`
//!
//! as opposed to the common implementation using a hash map
//! which maps items to a variable counting the number of occurances:
//!  - `a -> 2`
//!  - `b -> 1`
//!
//! ---
//!
//! Storing elements as a flattened hash table ***can*** have the benefit
//! that it saves space compared to the common implementations.
//! This ***can*** be the case when there are very few duplicates and/or the size of the elements is very small.

/// Multimap implementation where entries are stored as a flattened hash map.
pub mod map;

/// Multiset implementation where items are stored as a flattened hash set.
pub mod set;

#[cfg(feature = "rayon")]
mod rayon;

#[cfg(feature = "serde")]
mod serde;

pub use hashbrown::TryReserveError;
pub use map::FlatMultimap;
pub use set::FlatMultiset;
