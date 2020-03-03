use crate::{
    lhs_types::AsRefIterator,
    types::{BytesOrString, GetType, LhsValue, LhsValueSeed, Type, TypeMismatchError},
};
use serde::{
    de::{self, DeserializeSeed, Deserializer, MapAccess, SeqAccess, Visitor},
    ser::{SerializeMap, SerializeSeq},
    Serialize, Serializer,
};
use std::{borrow::Cow, collections::HashMap, fmt, ops::Deref};

#[derive(Debug, Clone, PartialEq, Eq)]
enum InnerMap<'a> {
    Owned(HashMap<Box<[u8]>, LhsValue<'a>>),
    Borrowed(&'a HashMap<Box<[u8]>, LhsValue<'a>>),
}

impl<'a> InnerMap<'a> {
    fn get_mut(&mut self, key: &[u8]) -> Option<&mut LhsValue<'a>> {
        if let InnerMap::Borrowed(map) = self {
            *self = InnerMap::Owned(map.clone());
        }
        match self {
            InnerMap::Owned(map) => map.get_mut(key),
            InnerMap::Borrowed(_) => unreachable!(),
        }
    }

    fn insert(&mut self, key: &[u8], value: LhsValue<'a>) {
        if let InnerMap::Borrowed(map) = self {
            *self = InnerMap::Owned(map.clone());
        }
        match self {
            InnerMap::Owned(map) => map.insert(key.to_vec().into_boxed_slice(), value),
            InnerMap::Borrowed(_) => unreachable!(),
        };
    }
}

impl<'a> Deref for InnerMap<'a> {
    type Target = HashMap<Box<[u8]>, LhsValue<'a>>;

    fn deref(&self) -> &Self::Target {
        match self {
            InnerMap::Owned(ref map) => &map,
            InnerMap::Borrowed(ref_map) => ref_map,
        }
    }
}

/// A map of string to [`Type`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Map<'a> {
    val_type: Cow<'a, Type>,
    data: InnerMap<'a>,
}

impl<'a> Map<'a> {
    /// Creates a new map
    pub fn new(val_type: Type) -> Self {
        Self {
            val_type: Cow::Owned(val_type),
            data: InnerMap::Owned(HashMap::new()),
        }
    }

    /// Get a reference to an element if it exists
    pub fn get(&self, key: &[u8]) -> Option<&LhsValue<'a>> {
        self.data.get(key)
    }

    /// Get a mutable reference to an element if it exists
    pub fn get_mut(&mut self, key: &[u8]) -> Option<&mut LhsValue<'a>> {
        self.data.get_mut(key)
    }

    /// Inserts an element, returns the previously inserted
    /// element if it exists.
    pub fn insert(&mut self, key: &[u8], value: LhsValue<'a>) -> Result<(), TypeMismatchError> {
        let value_type = value.get_type();
        if *self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone().into_owned().into(),
                actual: value_type,
            });
        }
        self.data.insert(key, value);
        Ok(())
    }

    pub(crate) fn as_ref(&'a self) -> Map<'a> {
        Map {
            val_type: self.val_type.clone(),
            data: match self.data {
                InnerMap::Owned(ref map) => InnerMap::Borrowed(map),
                InnerMap::Borrowed(ref_map) => InnerMap::Borrowed(ref_map),
            },
        }
    }

    /// Returns the type of the contained values.
    pub fn value_type(&self) -> &Type {
        &self.val_type
    }

    /// Returns the number of elements in the map
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Convert current map into an iterator over contained values
    pub fn values_into_iter(self) -> MapValuesIntoIter<'a> {
        let Map { data, .. } = self;
        match data {
            InnerMap::Owned(map) => MapValuesIntoIter::Owned(map.into_iter()),
            InnerMap::Borrowed(map) => {
                MapValuesIntoIter::Borrowed(AsRefIterator::new(map.values()))
            }
        }
    }

    pub(crate) fn extract(self, key: &[u8]) -> Option<LhsValue<'a>> {
        let Self { data, .. } = self;
        match data {
            InnerMap::Owned(mut map) => map.remove(key),
            InnerMap::Borrowed(map) => map.get(key).map(LhsValue::as_ref),
        }
    }

    /// Creates an iterator visiting all key-value pairs in arbitrary order.
    pub fn iter(&self) -> MapIter<'a, '_> {
        MapIter(self.data.iter())
    }
}

impl<'a> GetType for Map<'a> {
    fn get_type(&self) -> Type {
        Type::Map(Box::new(self.val_type.clone().into_owned()))
    }
}

pub struct MapIter<'a, 'b>(std::collections::hash_map::Iter<'b, Box<[u8]>, LhsValue<'a>>);

impl<'a, 'b> Iterator for MapIter<'a, 'b> {
    type Item = (&'b [u8], &'b LhsValue<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (&**k, v))
    }
}

pub enum MapValuesIntoIter<'a> {
    Owned(std::collections::hash_map::IntoIter<Box<[u8]>, LhsValue<'a>>),
    Borrowed(AsRefIterator<'a, std::collections::hash_map::Values<'a, Box<[u8]>, LhsValue<'a>>>),
}

impl<'a> Iterator for MapValuesIntoIter<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MapValuesIntoIter::Owned(iter) => iter.next().map(|(_, v)| v),
            MapValuesIntoIter::Borrowed(iter) => iter.next(),
        }
    }
}

impl<'a> IntoIterator for Map<'a> {
    type Item = (Box<[u8]>, LhsValue<'a>);
    type IntoIter = std::collections::hash_map::IntoIter<Box<[u8]>, LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        match self.data {
            InnerMap::Owned(map) => map.into_iter(),
            InnerMap::Borrowed(ref_map) => ref_map.clone().into_iter(),
        }
    }
}

impl<'a> Serialize for Map<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let to_map = self.data.keys().all(|key| std::str::from_utf8(key).is_ok());

        if to_map {
            let mut map = serializer.serialize_map(Some(self.len()))?;
            for (k, v) in self.data.iter() {
                map.serialize_entry(std::str::from_utf8(k).unwrap(), v)?;
            }
            map.end()
        } else {
            // Keys have to be sorted in order to have reproducible output
            let mut keys = Vec::new();
            for key in self.data.keys() {
                keys.push(key)
            }
            keys.sort();
            let mut seq = serializer.serialize_seq(Some(self.len()))?;
            for key in keys {
                seq.serialize_element(&[
                    &LhsValue::Bytes((&**key).into()),
                    self.data.get(key).unwrap(),
                ])?;
            }
            seq.end()
        }
    }
}

struct MapEntrySeed<'a>(&'a Type);

impl<'de, 'a> DeserializeSeed<'de> for MapEntrySeed<'a> {
    type Value = (Cow<'de, [u8]>, LhsValue<'de>);

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapEntryVisitor<'a>(&'a Type);

        impl<'de, 'a> Visitor<'de> for MapEntryVisitor<'a> {
            type Value = (Cow<'de, [u8]>, LhsValue<'de>);

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a [key, lhs value] pair")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let key = seq
                    .next_element::<BytesOrString<'_>>()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let value = seq
                    .next_element_seed(LhsValueSeed(self.0))?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok((key.into_bytes(), value))
            }
        }

        deserializer.deserialize_seq(MapEntryVisitor(self.0))
    }
}

impl<'de, 'a> DeserializeSeed<'de> for &'a mut Map<'de> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapVisitor<'de, 'a>(&'a mut Map<'de>);

        impl<'de, 'a> Visitor<'de> for MapVisitor<'de, 'a> {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    formatter,
                    "a map of lhs value or an array of pair of lhs value"
                )
            }

            fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
            where
                M: MapAccess<'de>,
            {
                while let Some(key) = access.next_key::<Cow<'_, str>>()? {
                    let value = access.next_value_seed(LhsValueSeed(self.0.value_type()))?;
                    self.0.insert(key.as_bytes(), value).map_err(|e| {
                        de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            e.actual, e.expected
                        ))
                    })?;
                }

                Ok(())
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                while let Some(entry) = seq.next_element_seed(MapEntrySeed(self.0.value_type()))? {
                    self.0.insert(&entry.0, entry.1).map_err(|e| {
                        de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            e.actual, e.expected
                        ))
                    })?;
                }
                Ok(())
            }
        }

        deserializer.deserialize_struct("", &[], MapVisitor(self))
    }
}
