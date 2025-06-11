use crate::{
    TypeMismatchError,
    lhs_types::AsRefIterator,
    types::{BytesOrString, CompoundType, GetType, IntoValue, LhsValue, LhsValueSeed, Type},
};
use serde::{
    Serialize, Serializer,
    de::{self, DeserializeSeed, Deserializer, MapAccess, SeqAccess, Visitor},
    ser::{SerializeMap, SerializeSeq},
};
use std::{
    borrow::Cow,
    collections::BTreeMap,
    fmt,
    hash::{Hash, Hasher},
    hint::unreachable_unchecked,
    ops::Deref,
};

use super::{TypedArray, array::InnerArray};

#[derive(Debug, Clone)]
pub(crate) enum InnerMap<'a> {
    Owned(BTreeMap<Box<[u8]>, LhsValue<'a>>),
    Borrowed(&'a BTreeMap<Box<[u8]>, LhsValue<'a>>),
}

impl<'a> InnerMap<'a> {
    #[inline]
    const fn new() -> Self {
        Self::Owned(BTreeMap::new())
    }

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
        Self::new()
    }
}

/// A map of string to [`Type`].
#[derive(Debug, Clone)]
pub struct Map<'a> {
    val_type: CompoundType,
    pub(crate) data: InnerMap<'a>,
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
    pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<&LhsValue<'a>> {
        self.data.get(key.as_ref())
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

    /// Creates a new map from the specified iterator.
    pub fn try_from_iter<E: From<TypeMismatchError>, V: Into<LhsValue<'a>>>(
        val_type: impl Into<CompoundType>,
        iter: impl IntoIterator<Item = Result<(Box<[u8]>, V), E>>,
    ) -> Result<Self, E> {
        let val_type = val_type.into();
        iter.into_iter()
            .map(|key_val| {
                key_val.and_then(|(key, val)| {
                    let elem = val.into();
                    let elem_type = elem.get_type();
                    if val_type != elem_type.into() {
                        Err(E::from(TypeMismatchError {
                            expected: Type::from(val_type).into(),
                            actual: elem_type,
                        }))
                    } else {
                        Ok((key, elem))
                    }
                })
            })
            .collect::<Result<BTreeMap<_, _>, _>>()
            .map(|map| Map {
                val_type,
                data: InnerMap::Owned(map),
            })
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
                let value_type = self.0.value_type();
                while let Some(key) = access.next_key::<Cow<'_, str>>()? {
                    let value = access.next_value_seed(LhsValueSeed(&value_type))?;
                    if value.get_type() != value_type {
                        return Err(de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            value.get_type(),
                            value_type
                        )));
                    }
                    self.0
                        .data
                        .insert(key.into_owned().into_bytes().into(), value);
                }

                Ok(())
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let value_type = self.0.value_type();
                while let Some((key, value)) = seq.next_element_seed(MapEntrySeed(&value_type))? {
                    if value.get_type() != value_type {
                        return Err(de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            value.get_type(),
                            value_type
                        )));
                    }
                    self.0.data.insert(key.into_owned().into(), value);
                }
                Ok(())
            }
        }

        deserializer.deserialize_struct("", &[], MapVisitor(self))
    }
}

/// Typed wrapper over a `Map` which provides
/// infaillible operations.
#[repr(transparent)]
pub struct TypedMap<'a, V>
where
    V: IntoValue<'a>,
{
    map: InnerMap<'a>,
    _marker: std::marker::PhantomData<BTreeMap<Box<[u8]>, V>>,
}

impl<'a, V: IntoValue<'a>> TypedMap<'a, V> {
    /// Creates a new empty typed map.
    #[inline]
    pub const fn new() -> Self {
        const {
            Self {
                map: InnerMap::new(),
                _marker: std::marker::PhantomData,
            }
        }
    }

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

    /// Converts the strongly typed map into a borrowed loosely typed map.
    pub fn as_map(&'a self) -> Map<'a> {
        Map {
            val_type: V::TYPE.into(),
            data: InnerMap::Borrowed(self.map.deref()),
        }
    }
}

impl<'a, V: IntoValue<'a>> fmt::Debug for TypedMap<'a, V> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_map().entries(self.map.iter()).finish()
    }
}

impl<'a, V: IntoValue<'a>> PartialEq for TypedMap<'a, V> {
    fn eq(&self, other: &Self) -> bool {
        self.map.deref() == other.map.deref()
    }
}

impl<'a, 'k, V: Copy + IntoValue<'a>, S: AsRef<[(&'k [u8], V)]>> PartialEq<S> for TypedMap<'a, V> {
    fn eq(&self, other: &S) -> bool {
        other
            .as_ref()
            .iter()
            .copied()
            .map(|(k, v)| (k, v.into_value()))
            .eq(self.map.iter().map(|(k, v)| (&**k, v.as_ref())))
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
        Self::new()
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

impl<'a, V: IntoValue<'a>> TypedMap<'a, TypedMap<'a, V>> {
    /// Returns a reference to the value corresponding to the key.
    pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<&TypedMap<'a, V>> {
        self.map.get(key.as_ref()).map(|val| match val {
            LhsValue::Map(map) => {
                // Safety: this is safe because `TypedMap` is a repr(transparent)
                // newtype over `InnerMap`.
                unsafe { std::mem::transmute::<&InnerMap<'a>, &TypedMap<'a, V>>(&map.data) }
            }
            _ => unreachable!(),
        })
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<K: AsRef<[u8]>>(&mut self, key: K) -> Option<&mut TypedMap<'a, V>> {
        self.map.get_mut(key.as_ref()).map(|val| match val {
            LhsValue::Map(map) => {
                // Safety: this is safe because `TypedMap` is a repr(transparent)
                // newtype over `InnerMap`.
                unsafe {
                    std::mem::transmute::<&mut InnerMap<'a>, &mut TypedMap<'a, V>>(&mut map.data)
                }
            }
            _ => unreachable!(),
        })
    }

    /// Returns a mutable reference to the value coressponding to the key or insert a new one.
    pub fn get_or_insert(
        &mut self,
        key: Box<[u8]>,
        value: TypedMap<'a, V>,
    ) -> &mut TypedMap<'a, V> {
        match self.map.get_or_insert(key, value.into_value()) {
            LhsValue::Map(map) => {
                // Safety: this is safe because `TypedMap` is a repr(transparent)
                // newtype over `InnerMap`.
                unsafe {
                    std::mem::transmute::<&mut InnerMap<'a>, &mut TypedMap<'a, V>>(&mut map.data)
                }
            }
            _ => unreachable!(),
        }
    }
}

impl<'a, V: IntoValue<'a>> TypedMap<'a, TypedArray<'a, V>> {
    /// Returns a reference to the value corresponding to the key.
    pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<&TypedArray<'a, V>> {
        self.map.get(key.as_ref()).map(|val| match val {
            LhsValue::Array(array) => {
                // Safety: this is safe because `TypedArray` is a repr(transparent)
                // newtype over `InnerArray`.
                unsafe { std::mem::transmute::<&InnerArray<'a>, &TypedArray<'a, V>>(&array.data) }
            }
            _ => unreachable!(),
        })
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<K: AsRef<[u8]>>(&mut self, key: K) -> Option<&mut TypedArray<'a, V>> {
        self.map.get_mut(key.as_ref()).map(|val| match val {
            LhsValue::Array(array) => {
                // Safety: this is safe because `TypedArray` is a repr(transparent)
                // newtype over `InnerArray`.
                unsafe {
                    std::mem::transmute::<&mut InnerArray<'a>, &mut TypedArray<'a, V>>(
                        &mut array.data,
                    )
                }
            }
            _ => unreachable!(),
        })
    }

    /// Returns a mutable reference to the value coressponding to the key or insert a new one.
    pub fn get_or_insert(
        &mut self,
        key: Box<[u8]>,
        value: TypedArray<'a, V>,
    ) -> &mut TypedArray<'a, V> {
        match self.map.get_or_insert(key, value.into_value()) {
            LhsValue::Array(array) => {
                // Safety: this is safe because `TypedArray` is a repr(transparent)
                // newtype over `InnerArray`.
                unsafe {
                    std::mem::transmute::<&mut InnerArray<'a>, &mut TypedArray<'a, V>>(
                        &mut array.data,
                    )
                }
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size_of_map() {
        assert_eq!(std::mem::size_of::<Map<'_>>(), 40);
    }

    #[test]
    fn test_borrowed_eq_owned() {
        let mut map = TypedMap::new();

        map.insert("key".as_bytes().to_vec().into(), "borrowed");

        let owned = Map::from(map);

        let borrowed = owned.as_ref();

        assert!(matches!(owned.data, InnerMap::Owned(_)));

        assert!(matches!(borrowed.data, InnerMap::Borrowed(_)));

        assert_eq!(owned, borrowed);

        assert_eq!(borrowed, borrowed.to_owned());
    }

    fn key(s: &str) -> Box<[u8]> {
        s.as_bytes().to_vec().into_boxed_slice()
    }

    #[test]
    fn test_typed_map_get_typed_map() {
        let mut map = TypedMap::from_iter([
            (
                key("first"),
                TypedMap::from_iter([(key("a"), 42), (key("b"), 1337), (key("c"), 0)]),
            ),
            (
                key("second"),
                TypedMap::from_iter([(key("d"), 7), (key("e"), 3)]),
            ),
        ]);

        assert_eq!(
            *map.get("first").unwrap(),
            [(b"a" as &[u8], 42), (b"b", 1337), (b"c", 0)]
        );

        assert_eq!(*map.get("second").unwrap(), [(b"d" as &[u8], 7), (b"e", 3)]);

        map.get_mut("second").unwrap().insert(key("f"), 99);

        assert_eq!(
            *map.get("second").unwrap(),
            [(b"d" as &[u8], 7), (b"e", 3), (b"f", 99)]
        );
    }

    #[test]
    fn test_typed_map_get_typed_array() {
        let mut map = TypedMap::from_iter([
            (key("first"), TypedArray::from_iter(["a", "b", "c"])),
            (key("second"), TypedArray::from_iter(["d", "e"])),
        ]);

        assert_eq!(*map.get("first").unwrap(), ["a", "b", "c"]);

        assert_eq!(*map.get("second").unwrap(), ["d", "e"]);

        map.get_mut("second").unwrap().push("f");

        assert_eq!(*map.get("second").unwrap(), ["d", "e", "f"]);
    }
}
