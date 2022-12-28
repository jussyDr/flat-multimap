use crate::{FlatMultimap, FlatMultiset};
use serde::{Serialize, Serializer};

impl<K, V, H> Serialize for FlatMultimap<K, V, H>
where
    K: Serialize,
    V: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_map(self)
    }
}

impl<T, H> Serialize for FlatMultiset<T, H>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.collect_seq(self)
    }
}
