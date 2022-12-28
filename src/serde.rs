use crate::{FlatMultimap, FlatMultiset};
use serde::de::{MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::marker::PhantomData;

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

impl<'de, K, V, S> Deserialize<'de> for FlatMultimap<K, V, S>
where
    K: Deserialize<'de> + Eq + Hash,
    V: Deserialize<'de>,
    S: BuildHasher + Default,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapVisitor<K, V, S> {
            marker: PhantomData<FlatMultimap<K, V, S>>,
        }

        impl<'de, K, V, S> Visitor<'de> for MapVisitor<K, V, S>
        where
            K: Deserialize<'de> + Eq + Hash,
            V: Deserialize<'de>,
            S: BuildHasher + Default,
        {
            type Value = FlatMultimap<K, V, S>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a map")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = FlatMultimap::with_capacity_and_hasher(
                    map.size_hint().unwrap_or(0),
                    S::default(),
                );

                while let Some((key, value)) = map.next_entry()? {
                    values.insert(key, value);
                }

                Ok(values)
            }
        }

        let visitor = MapVisitor {
            marker: PhantomData,
        };

        deserializer.deserialize_map(visitor)
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

impl<'de, T, S> Deserialize<'de> for FlatMultiset<T, S>
where
    T: Deserialize<'de> + Eq + Hash,
    S: BuildHasher + Default,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SeqVisitor<T, S> {
            marker: PhantomData<FlatMultiset<T, S>>,
        }

        impl<'de, T, S> Visitor<'de> for SeqVisitor<T, S>
        where
            T: Deserialize<'de> + Eq + Hash,
            S: BuildHasher + Default,
        {
            type Value = FlatMultiset<T, S>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = FlatMultiset::with_capacity_and_hasher(
                    seq.size_hint().unwrap_or(0),
                    S::default(),
                );

                while let Some(value) = seq.next_element()? {
                    values.insert(value);
                }

                Ok(values)
            }
        }

        let visitor = SeqVisitor {
            marker: PhantomData,
        };
        deserializer.deserialize_seq(visitor)
    }

    fn deserialize_in_place<D>(deserializer: D, place: &mut Self) -> Result<(), D::Error>
    where
        D: Deserializer<'de>,
    {
        struct SeqInPlaceVisitor<'a, T, S>(&'a mut FlatMultiset<T, S>);

        impl<'a, 'de, T, S> Visitor<'de> for SeqInPlaceVisitor<'a, T, S>
        where
            T: Deserialize<'de> + Eq + Hash,
            S: BuildHasher + Default,
        {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            #[cfg_attr(feature = "inline-more", inline)]
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                self.0.clear();
                self.0.reserve(seq.size_hint().unwrap_or(0));

                while let Some(value) = seq.next_element()? {
                    self.0.insert(value);
                }

                Ok(())
            }
        }

        deserializer.deserialize_seq(SeqInPlaceVisitor(place))
    }
}
