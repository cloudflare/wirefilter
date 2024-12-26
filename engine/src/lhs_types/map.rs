use crate::{
    lhs_types::AsRefIterator,
    types::{
        BytesOrString, CompoundType, GetType, IntoValue, LhsValue, LhsValueMut, LhsValueSeed, Type,
        TypeMismatchError,
    },
};
use serde::{
    de::{self, DeserializeSeed, Deserializer, MapAccess, SeqAccess, Visitor},
    ser::{SerializeMap, SerializeSeq},
    Serialize, Serializer,
};
use std::{
    borrow::Cow,
    collections::BTreeMap,
    fmt,
    hash::{Hash, Hasher},
    hint::unreachable_unchecked,
    ops::Deref,
};

#[derive(Debug, Clone)]
enum InnerMap<'a> {
    Owned(BTreeMap<Box<[u8]>, LhsValue<'a>>),
    Borrowed(&'a BTreeMap<Box<[u8]>, LhsValue<'a>>),
}

impl<'a> InnerMap<'a> {
    #[inline]
    fn as_map(&mut self) -> &mut BTreeMap<Box<[u8]>, LhsValue<'a>> {
        match self {
            InnerMap::Owned(map) => map,
            InnerMap::Borrowed(map) => {
                *self = InnerMap::Owned(map.clone());
                match self {
                    InnerMap::Owned(map) => map,
                    _ => unsafe { unreachable_unchecked() },
                }
            }
        }
    }

    #[inline]
    fn get_mut(&mut self, key: &[u8]) -> Option<&mut LhsValue<'a>> {
        self.as_map().get_mut(key)
    }

    #[inline]
    fn insert(&mut self, key: Box<[u8]>, value: LhsValue<'a>) {
        self.as_map().insert(key, value);
    }

    #[inline]
    fn get_or_insert(&mut self, key: Box<[u8]>, value: LhsValue<'a>) -> &mut LhsValue<'a> {
        self.as_map().entry(key).or_insert(value)
    }
}

impl<'a> Deref for InnerMap<'a> {
    type Target = BTreeMap<Box<[u8]>, LhsValue<'a>>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        match self {
            InnerMap::Owned(map) => map,
            InnerMap::Borrowed(ref_map) => ref_map,
        }
    }
}

impl Default for InnerMap<'_> {
    fn default() -> Self {
        Self::Owned(BTreeMap::new())
    }
}

/// A map of string to [`Type`].
#[derive(Debug, Clone)]
pub struct Map<'a> {
    val_type: CompoundType,
    data: InnerMap<'a>,
}

impl<'a> Map<'a> {
    /// Creates a new map
    pub fn new(val_type: impl Into<CompoundType>) -> Self {
        Self {
            val_type: val_type.into(),
            data: InnerMap::Owned(BTreeMap::new()),
        }
    }

    /// Get a reference to an element if it exists
    pub fn get(&self, key: &[u8]) -> Option<&LhsValue<'a>> {
        self.data.get(key)
    }

    /// Get a mutable reference to an element if it exists
    pub fn get_mut(&mut self, key: &[u8]) -> Option<LhsValueMut<'_, 'a>> {
        self.data.get_mut(key).map(LhsValueMut::from)
    }

    /// Inserts an element, overwriting if one already exists
    pub fn insert(
        &mut self,
        key: &[u8],
        value: impl Into<LhsValue<'a>>,
    ) -> Result<(), TypeMismatchError> {
        let value = value.into();
        let value_type = value.get_type();
        if value_type != self.val_type.into() {
            return Err(TypeMismatchError {
                expected: Type::from(self.val_type).into(),
                actual: value_type,
            });
        }
        self.data.insert(key.into(), value);
        Ok(())
    }

    /// Inserts `value` if `key` is missing, then returns a mutable reference to the contained value.
    pub fn get_or_insert(
        &mut self,
        key: Box<[u8]>,
        value: impl Into<LhsValue<'a>>,
    ) -> Result<LhsValueMut<'_, 'a>, TypeMismatchError> {
        let value = value.into();
        let value_type = value.get_type();
        if value_type != self.val_type.into() {
            return Err(TypeMismatchError {
                expected: Type::from(self.val_type).into(),
                actual: value_type,
            });
        }
        Ok(LhsValueMut::from(self.data.get_or_insert(key, value)))
    }

    pub(crate) fn as_ref(&'a self) -> Map<'a> {
        Map {
            val_type: self.val_type,
            data: match self.data {
                InnerMap::Owned(ref map) => InnerMap::Borrowed(map),
                InnerMap::Borrowed(ref_map) => InnerMap::Borrowed(ref_map),
            },
        }
    }

    /// Converts a `Map` with borrowed data to a fully owned `Map`.
    pub fn into_owned(self) -> Map<'static> {
        Map {
            val_type: self.val_type,
            data: match self.data {
                InnerMap::Owned(map) => InnerMap::Owned(
                    map.into_iter()
                        .map(|(key, val)| (key, val.into_owned()))
                        .collect(),
                ),
                InnerMap::Borrowed(map) => InnerMap::Owned(
                    map.iter()
                        .map(|(key, value)| (key.clone(), value.clone().into_owned()))
                        .collect(),
                ),
            },
        }
    }

    /// Returns the type of the contained values.
    pub fn value_type(&self) -> Type {
        self.val_type.into()
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
    #[inline]
    pub fn iter(&self) -> MapIter<'a, '_> {
        MapIter(self.data.iter())
    }
}

impl<'a> PartialEq for Map<'a> {
    #[inline]
    fn eq(&self, other: &Map<'a>) -> bool {
        self.val_type == other.val_type && self.data.deref() == other.data.deref()
    }
}

impl Eq for Map<'_> {}

impl GetType for Map<'_> {
    #[inline]
    fn get_type(&self) -> Type {
        Type::Map(self.val_type)
    }
}

impl Hash for Map<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_type().hash(state);
        self.data.deref().hash(state);
    }
}

/// An iterator over the entries of a Map.
pub struct MapIter<'a, 'b>(std::collections::btree_map::Iter<'b, Box<[u8]>, LhsValue<'a>>);

impl<'a, 'b> Iterator for MapIter<'a, 'b> {
    type Item = (&'b [u8], &'b LhsValue<'a>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, v)| (&**k, v))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for MapIter<'_, '_> {
    #[inline]
    fn len(&self) -> usize {
        self.0.len()
    }
}

pub enum MapValuesIntoIter<'a> {
    Owned(std::collections::btree_map::IntoIter<Box<[u8]>, LhsValue<'a>>),
    Borrowed(AsRefIterator<'a, std::collections::btree_map::Values<'a, Box<[u8]>, LhsValue<'a>>>),
}

impl<'a> Iterator for MapValuesIntoIter<'a> {
    type Item = LhsValue<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MapValuesIntoIter::Owned(iter) => iter.next().map(|(_, v)| v),
            MapValuesIntoIter::Borrowed(iter) => iter.next(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for MapValuesIntoIter<'_> {
    fn len(&self) -> usize {
        match self {
            MapValuesIntoIter::Owned(iter) => iter.len(),
            MapValuesIntoIter::Borrowed(iter) => iter.len(),
        }
    }
}

impl<'a> IntoIterator for Map<'a> {
    type Item = (Box<[u8]>, LhsValue<'a>);
    type IntoIter = std::collections::btree_map::IntoIter<Box<[u8]>, LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        match self.data {
            InnerMap::Owned(map) => map.into_iter(),
            InnerMap::Borrowed(ref_map) => ref_map.clone().into_iter(),
        }
    }
}

impl<'a, 'b> IntoIterator for &'b Map<'a> {
    type Item = (&'b [u8], &'b LhsValue<'a>);
    type IntoIter = MapIter<'a, 'b>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        MapIter(self.data.deref().iter())
    }
}

impl Serialize for Map<'_> {
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

impl<'de> DeserializeSeed<'de> for MapEntrySeed<'_> {
    type Value = (Cow<'de, [u8]>, LhsValue<'de>);

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapEntryVisitor<'a>(&'a Type);

        impl<'de> Visitor<'de> for MapEntryVisitor<'_> {
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

impl<'de> DeserializeSeed<'de> for &mut Map<'de> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapVisitor<'de, 'a>(&'a mut Map<'de>);

        impl<'de> Visitor<'de> for MapVisitor<'de, '_> {
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
                    let value = access.next_value_seed(LhsValueSeed(&self.0.value_type()))?;
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
                while let Some(entry) = seq.next_element_seed(MapEntrySeed(&self.0.value_type()))? {
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

/// Wrapper type around mutable `Map` to prevent
/// illegal operations like changing the type of
/// its values.
pub struct MapMut<'a, 'b>(&'a mut Map<'b>);

impl<'a, 'b> MapMut<'a, 'b> {
    /// Get a mutable reference to an element if it exists
    #[inline]
    pub fn get_mut(&'a mut self, key: &[u8]) -> Option<LhsValueMut<'a, 'b>> {
        self.0.get_mut(key).map(LhsValueMut::from)
    }

    /// Inserts an element, overwriting if one already exists
    #[inline]
    pub fn insert(
        &mut self,
        key: &[u8],
        value: impl Into<LhsValue<'b>>,
    ) -> Result<(), TypeMismatchError> {
        self.0.insert(key, value)
    }

    /// Inserts `value` if `key` is missing, then returns a mutable reference to the contained value.
    #[inline]
    pub fn get_or_insert(
        &'a mut self,
        key: Box<[u8]>,
        value: impl Into<LhsValue<'b>>,
    ) -> Result<LhsValueMut<'a, 'b>, TypeMismatchError> {
        self.0.get_or_insert(key, value)
    }
}

impl<'b> Deref for MapMut<'_, 'b> {
    type Target = Map<'b>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, 'b> From<&'a mut Map<'b>> for MapMut<'a, 'b> {
    #[inline]
    fn from(map: &'a mut Map<'b>) -> Self {
        Self(map)
    }
}

/// Typed wrapper over a `Map` which provides
/// infaillible operations.
#[derive(Debug)]
pub struct TypedMap<'a, V>
where
    V: IntoValue<'a>,
{
    map: InnerMap<'a>,
    _marker: std::marker::PhantomData<BTreeMap<Box<[u8]>, V>>,
}

impl<'a, V: IntoValue<'a>> TypedMap<'a, V> {
    /// Push an element to the back of the map
    #[inline]
    pub fn insert(&mut self, key: Box<[u8]>, value: V) {
        self.map.insert(key, value.into_value())
    }

    /// Returns the number of elements in the array
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns true if the array contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<'a, V: IntoValue<'a>> From<TypedMap<'a, V>> for Map<'a> {
    #[inline]
    fn from(value: TypedMap<'a, V>) -> Self {
        Self {
            val_type: V::TYPE.into(),
            data: value.map,
        }
    }
}

impl<'a, V: IntoValue<'a>> Default for TypedMap<'a, V> {
    #[inline]
    fn default() -> Self {
        Self {
            map: InnerMap::default(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, V: IntoValue<'a>> Extend<(Box<[u8]>, V)> for TypedMap<'a, V> {
    #[inline]
    fn extend<T: IntoIterator<Item = (Box<[u8]>, V)>>(&mut self, iter: T) {
        self.map
            .as_map()
            .extend(iter.into_iter().map(|(k, v)| (k, v.into_value())))
    }
}

impl<'a, V: IntoValue<'a>> FromIterator<(Box<[u8]>, V)> for TypedMap<'a, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Box<[u8]>, V)>,
    {
        Self {
            map: InnerMap::Owned(iter.into_iter().map(|(k, v)| (k, v.into_value())).collect()),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, V: IntoValue<'a>> IntoValue<'a> for TypedMap<'a, V> {
    const TYPE: Type = Type::Map(CompoundType::from_type(V::TYPE));

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Map(self.into())
    }
}

#[test]
fn test_size_of_map() {
    assert_eq!(std::mem::size_of::<Map<'_>>(), 40);
}

#[test]
fn test_borrowed_eq_owned() {
    let mut owned = Map::new(Type::Bytes);

    owned
        .insert(b"key", LhsValue::Bytes("borrowed".as_bytes().into()))
        .unwrap();

    let borrowed = owned.as_ref();

    assert!(matches!(owned.data, InnerMap::Owned(_)));

    assert!(matches!(borrowed.data, InnerMap::Borrowed(_)));

    assert_eq!(owned, borrowed);

    assert_eq!(borrowed, borrowed.to_owned());
}
