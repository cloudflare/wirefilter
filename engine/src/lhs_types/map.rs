use super::TypedArray;
use super::array::InnerArray;
use crate::TypeMismatchError;
use crate::lhs_types::{AsRefIterator, Bytes};
use crate::types::{CompoundType, GetType, IntoValue, LhsValue, LhsValueSeed, Type};
use ahash::RandomState;
#[cfg(feature = "get-size2")]
use get_size2::{GetSize, GetSizeTracker};
use indexmap::IndexMap;
use serde::de::{self, DeserializeSeed, Deserializer, MapAccess, SeqAccess, Visitor};
use serde::ser::{SerializeMap, SerializeSeq};
use serde::{Serialize, Serializer};
use std::fmt;
use std::hash::{Hash, Hasher};

type MapData<'a> = IndexMap<Bytes<'a>, LhsValue<'a>, RandomState>;

#[derive(Debug, Clone)]
pub(crate) enum InnerMap<'a> {
    // Boxing avoids increasing the size of every LhsValue.
    Owned(Box<MapData<'a>>),
    Borrowed(&'a MapData<'a>),
}

#[cfg(feature = "get-size2")]
impl GetSize for InnerMap<'_> {
    fn get_heap_size_with_tracker<T: GetSizeTracker>(&self, tracker: T) -> (usize, T) {
        match self {
            Self::Owned(values) => values.get_heap_size_with_tracker(tracker),
            Self::Borrowed(_) => (0, tracker),
        }
    }
}

impl<'a> InnerMap<'a> {
    #[inline]
    fn new() -> Self {
        Self::Owned(Box::default())
    }

    fn to_mut(&mut self) -> &mut MapData<'a> {
        if let Self::Borrowed(map) = self {
            *self = Self::Owned(Box::new(
                map.iter()
                    .map(|(key, value)| (Bytes::Borrowed(key), value.as_ref()))
                    .collect(),
            ));
        }
        match self {
            Self::Owned(map) => map,
            Self::Borrowed(_) => unreachable!(),
        }
    }

    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::Owned(map) => map.len(),
            Self::Borrowed(map) => map.len(),
        }
    }

    #[inline]
    fn is_empty(&self) -> bool {
        match self {
            Self::Owned(map) => map.is_empty(),
            Self::Borrowed(map) => map.is_empty(),
        }
    }

    #[inline]
    fn get<K: AsRef<[u8]>>(&self, key: K) -> Option<&LhsValue<'a>> {
        match self {
            Self::Owned(map) => map.get(key.as_ref()),
            Self::Borrowed(map) => map.get(key.as_ref()),
        }
    }

    #[inline]
    fn iter(&self) -> MapIter<'a, '_> {
        match self {
            Self::Owned(map) => MapIter(map.iter()),
            Self::Borrowed(map) => MapIter(map.iter()),
        }
    }
}

impl Default for InnerMap<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl Hash for InnerMap<'_> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Equality ignores insertion order, so combine entry hashes commutatively.
        // Fixed seeds make this independent of each map's lookup hasher.
        let entry_hasher = RandomState::with_seeds(0, 0, 0, 0);
        let mut entries_hash = 0_u64;
        for entry in self.iter() {
            entries_hash = entries_hash.wrapping_add(entry_hasher.hash_one(entry));
        }
        self.len().hash(state);
        entries_hash.hash(state);
    }
}

/// A map of string to [`Type`] that preserves insertion order.
#[derive(Debug, Clone)]
pub struct Map<'a> {
    val_type: CompoundType,
    pub(crate) data: InnerMap<'a>,
}

#[cfg(feature = "get-size2")]
impl GetSize for Map<'_> {
    fn get_heap_size_with_tracker<T: GetSizeTracker>(&self, tracker: T) -> (usize, T) {
        self.data.get_heap_size_with_tracker(tracker)
    }
}

impl<'a> Map<'a> {
    /// Creates a new map
    pub fn new(val_type: impl Into<CompoundType>) -> Self {
        Self {
            val_type: val_type.into(),
            data: InnerMap::new(),
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
                InnerMap::Owned(map) => InnerMap::Owned(Box::new(
                    (*map)
                        .into_iter()
                        .map(|(key, val)| (key.into_owned(), val.into_owned()))
                        .collect(),
                )),
                InnerMap::Borrowed(map) => InnerMap::Owned(Box::new(
                    map.iter()
                        .map(|(key, value)| (key.to_owned(), value.as_ref().into_owned()))
                        .collect(),
                )),
            },
        }
    }

    /// Returns the type of the contained values.
    #[inline]
    pub fn value_type(&self) -> Type {
        self.val_type.into()
    }

    /// Returns the number of elements in the map
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Convert current map into an iterator over contained values
    pub fn into_values(self) -> MapValuesIntoIter<'a> {
        let Map { data, .. } = self;
        match data {
            InnerMap::Owned(map) => MapValuesIntoIter::Owned((*map).into_iter()),
            InnerMap::Borrowed(map) => {
                MapValuesIntoIter::Borrowed(AsRefIterator::new(map.values()))
            }
        }
    }

    pub(crate) fn extract(self, key: &[u8]) -> Option<LhsValue<'a>> {
        let Self { data, .. } = self;
        match data {
            InnerMap::Owned(mut map) => map.shift_remove(key),
            InnerMap::Borrowed(map) => map.get(key).map(LhsValue::as_ref),
        }
    }

    /// Creates an iterator visiting all key-value pairs in insertion order.
    #[inline]
    pub fn iter(&self) -> MapIter<'a, '_> {
        self.data.iter()
    }

    /// Creates a new map from the specified iterator.
    pub fn try_from_iter<E: From<TypeMismatchError>, V: Into<LhsValue<'a>>>(
        val_type: impl Into<CompoundType>,
        iter: impl IntoIterator<Item = Result<(Bytes<'a>, V), E>>,
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
            .collect::<Result<MapData<'_>, _>>()
            .map(|map| Map {
                val_type,
                data: InnerMap::Owned(Box::new(map)),
            })
    }
}

impl<'a> PartialEq for Map<'a> {
    #[inline]
    fn eq(&self, other: &Map<'a>) -> bool {
        if self.val_type != other.val_type {
            return false;
        }

        if self.data.len() != other.data.len() {
            return false;
        }

        for (k, v) in self.data.iter() {
            if other.data.get(k) != Some(v) {
                return false;
            }
        }

        true
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
        self.data.hash(state);
    }
}

/// An iterator over the entries of a Map.
pub struct MapIter<'a, 'b>(indexmap::map::Iter<'b, Bytes<'a>, LhsValue<'a>>);

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
    Owned(indexmap::map::IntoIter<Bytes<'a>, LhsValue<'a>>),
    Borrowed(AsRefIterator<'a, indexmap::map::Values<'a, Bytes<'a>, LhsValue<'a>>>),
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
    #[inline]
    fn len(&self) -> usize {
        match self {
            MapValuesIntoIter::Owned(iter) => iter.len(),
            MapValuesIntoIter::Borrowed(iter) => iter.len(),
        }
    }
}

enum MapIntoIterImpl<'a> {
    Owned(indexmap::map::IntoIter<Bytes<'a>, LhsValue<'a>>),
    Borrowed(indexmap::map::Iter<'a, Bytes<'a>, LhsValue<'a>>),
}

/// An iterator yielding map entries in insertion order, preserving key ownership.
pub struct MapIntoIter<'a>(MapIntoIterImpl<'a>);

impl<'a> Iterator for MapIntoIter<'a> {
    type Item = (Bytes<'a>, LhsValue<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            MapIntoIter(MapIntoIterImpl::Owned(iter)) => iter.next(),
            MapIntoIter(MapIntoIterImpl::Borrowed(iter)) => {
                iter.next().map(|(k, v)| (Bytes::Borrowed(k), v.as_ref()))
            }
        }
    }
}

impl<'a> IntoIterator for Map<'a> {
    type IntoIter = MapIntoIter<'a>;
    type Item = (Bytes<'a>, LhsValue<'a>);

    fn into_iter(self) -> Self::IntoIter {
        match self.data {
            InnerMap::Owned(map) => MapIntoIter(MapIntoIterImpl::Owned((*map).into_iter())),
            InnerMap::Borrowed(map) => MapIntoIter(MapIntoIterImpl::Borrowed(map.iter())),
        }
    }
}

impl<'a, 'b> IntoIterator for &'b Map<'a> {
    type IntoIter = MapIter<'a, 'b>;
    type Item = (&'b [u8], &'b LhsValue<'a>);

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.data.iter()
    }
}

impl Serialize for Map<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let to_map = self
            .data
            .iter()
            .all(|(key, _)| std::str::from_utf8(key).is_ok());

        if to_map {
            let mut map = serializer.serialize_map(Some(self.len()))?;
            for (k, v) in self.data.iter() {
                map.serialize_entry(std::str::from_utf8(k).unwrap(), v)?;
            }
            map.end()
        } else {
            let mut seq = serializer.serialize_seq(Some(self.len()))?;
            for (key, value) in self.data.iter() {
                seq.serialize_element(&[&LhsValue::Bytes(key.into()), value])?;
            }
            seq.end()
        }
    }
}

struct MapEntrySeed<'a>(&'a Type);

impl<'de> DeserializeSeed<'de> for MapEntrySeed<'_> {
    type Value = (Bytes<'de>, LhsValue<'de>);

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapEntryVisitor<'a>(&'a Type);

        impl<'de> Visitor<'de> for MapEntryVisitor<'_> {
            type Value = (Bytes<'de>, LhsValue<'de>);

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a [key, lhs value] pair")
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let key = seq
                    .next_element::<Bytes<'_>>()?
                    .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                let value = seq
                    .next_element_seed(LhsValueSeed(self.0))?
                    .ok_or_else(|| de::Error::invalid_length(1, &self))?;
                Ok((key, value))
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
                let map = self.0.data.to_mut();
                while let Some(key) = access.next_key::<Bytes<'_>>()? {
                    let value = access.next_value_seed(LhsValueSeed(&value_type))?;
                    if value.get_type() != value_type {
                        return Err(de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            value.get_type(),
                            value_type
                        )));
                    }
                    map.insert(key, value);
                }

                Ok(())
            }

            fn visit_seq<V>(self, mut seq: V) -> Result<Self::Value, V::Error>
            where
                V: SeqAccess<'de>,
            {
                let value_type = self.0.value_type();
                let map = self.0.data.to_mut();
                while let Some((key, value)) = seq.next_element_seed(MapEntrySeed(&value_type))? {
                    if value.get_type() != value_type {
                        return Err(de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            value.get_type(),
                            value_type
                        )));
                    }
                    map.insert(key, value);
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
    _marker: std::marker::PhantomData<IndexMap<Bytes<'a>, V, RandomState>>,
}

impl<'a, V: IntoValue<'a>> TypedMap<'a, V> {
    /// Creates a new empty typed map.
    #[inline]
    pub fn new() -> Self {
        Self {
            map: InnerMap::new(),
            _marker: std::marker::PhantomData,
        }
    }

    #[inline]
    fn as_map_ref(&self) -> &MapData<'a> {
        match &self.map {
            InnerMap::Owned(map) => map,
            InnerMap::Borrowed(_) => unreachable!(),
        }
    }

    #[inline]
    fn as_map_mut(&mut self) -> &mut MapData<'a> {
        match &mut self.map {
            InnerMap::Owned(map) => map,
            InnerMap::Borrowed(_) => unreachable!(),
        }
    }

    /// Push an element to the back of the map
    #[inline]
    pub fn insert(&mut self, key: Bytes<'a>, value: V) {
        self.as_map_mut().insert(key, value.into_value());
    }

    /// Returns the number of elements in the array
    #[inline]
    pub fn len(&self) -> usize {
        self.as_map_ref().len()
    }

    /// Returns true if the array contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.as_map_ref().is_empty()
    }

    /// Converts the strongly typed map into a borrowed loosely typed map.
    pub fn as_map(&'a self) -> Map<'a> {
        Map {
            val_type: V::TYPE.into(),
            data: InnerMap::Borrowed(self.as_map_ref()),
        }
    }
}

impl<'a, V: IntoValue<'a>> fmt::Debug for TypedMap<'a, V> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_map().entries(self.as_map_ref().iter()).finish()
    }
}

impl<'a, V: IntoValue<'a>> PartialEq for TypedMap<'a, V> {
    fn eq(&self, other: &Self) -> bool {
        self.as_map_ref() == other.as_map_ref()
    }
}

impl<'a, 'k, V: Copy + IntoValue<'a>, S: AsRef<[(&'k [u8], V)]>> PartialEq<S> for TypedMap<'a, V> {
    fn eq(&self, other: &S) -> bool {
        other
            .as_ref()
            .iter()
            .copied()
            .map(|(k, v)| (k, v.into_value()))
            .eq(self.as_map_ref().iter().map(|(k, v)| (&**k, v.as_ref())))
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

impl<'a, V: IntoValue<'a>> Extend<(Bytes<'a>, V)> for TypedMap<'a, V> {
    #[inline]
    fn extend<T: IntoIterator<Item = (Bytes<'a>, V)>>(&mut self, iter: T) {
        self.as_map_mut()
            .extend(iter.into_iter().map(|(k, v)| (k, v.into_value())))
    }
}

impl<'a, V: IntoValue<'a>> FromIterator<(Bytes<'a>, V)> for TypedMap<'a, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Bytes<'a>, V)>,
    {
        Self {
            map: InnerMap::Owned(Box::new(
                iter.into_iter().map(|(k, v)| (k, v.into_value())).collect(),
            )),
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
        self.as_map_ref().get(key.as_ref()).map(|val| match val {
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
        self.as_map_mut()
            .get_mut(key.as_ref())
            .map(|val| match val {
                LhsValue::Map(map) => {
                    // Safety: this is safe because `TypedMap` is a repr(transparent)
                    // newtype over `InnerMap`.
                    unsafe {
                        std::mem::transmute::<&mut InnerMap<'a>, &mut TypedMap<'a, V>>(
                            &mut map.data,
                        )
                    }
                }
                _ => unreachable!(),
            })
    }

    /// Returns a mutable reference to the value coressponding to the key or insert a new one.
    pub fn get_or_insert(
        &mut self,
        key: Bytes<'a>,
        value: TypedMap<'a, V>,
    ) -> &mut TypedMap<'a, V> {
        match self.as_map_mut().entry(key).or_insert(value.into_value()) {
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
        self.as_map_ref().get(key.as_ref()).map(|val| match val {
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
        self.as_map_mut()
            .get_mut(key.as_ref())
            .map(|val| match val {
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
        key: Bytes<'a>,
        value: TypedArray<'a, V>,
    ) -> &mut TypedArray<'a, V> {
        match self.as_map_mut().entry(key).or_insert(value.into_value()) {
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

    fn key(s: &str) -> Bytes<'_> {
        s.as_bytes().to_vec().into()
    }

    #[test]
    fn test_size_of_map() {
        assert_eq!(std::mem::size_of::<Map<'_>>(), 24);
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

    #[test]
    fn test_clone_borrows_keys_and_values() {
        let key = b"key".to_vec();
        let value = b"value".to_vec();
        let map = Map::from(TypedMap::from_iter([(
            Bytes::Borrowed(&key),
            Bytes::Borrowed(&value),
        )]));
        let (cloned_key, cloned_value) = map.clone().into_iter().next().unwrap();
        let Bytes::Borrowed(cloned_key) = cloned_key else {
            panic!("cloning a borrowed key should keep it borrowed");
        };
        let LhsValue::Bytes(Bytes::Borrowed(cloned_value)) = cloned_value else {
            panic!("cloning a borrowed value should keep it borrowed");
        };
        assert!(std::ptr::eq(cloned_key, key.as_slice()));
        assert!(std::ptr::eq(cloned_value, value.as_slice()));
    }

    #[test]
    fn test_into_iter_ownership() {
        let map = Map::from(TypedMap::from_iter([(
            Bytes::from(b"key".to_vec()),
            Bytes::from(b"value".to_vec()),
        )]));
        let (key, LhsValue::Bytes(value)) = map.iter().next().unwrap() else {
            unreachable!();
        };
        let key_ptr = key.as_ptr();
        let value_ptr = value.as_ptr();

        let (key, value) = map.as_ref().clone().into_iter().next().unwrap();
        assert!(matches!(key, Bytes::Borrowed(_)));
        assert!(matches!(value, LhsValue::Bytes(Bytes::Borrowed(_))));
        assert_eq!(key.as_ptr(), key_ptr);
        let LhsValue::Bytes(value) = value else {
            unreachable!()
        };
        assert_eq!(value.as_ptr(), value_ptr);

        let (key, value) = map.into_iter().next().unwrap();
        assert!(matches!(key, Bytes::Owned(_)));
        assert!(matches!(value, LhsValue::Bytes(Bytes::Owned(_))));
        assert_eq!(key.as_ptr(), key_ptr);
        let LhsValue::Bytes(value) = value else {
            unreachable!()
        };
        assert_eq!(value.as_ptr(), value_ptr);
    }

    #[test]
    fn test_deserialize_borrowed_map_keeps_existing_entries_borrowed() {
        let map = Map::from(TypedMap::from_iter([(
            Bytes::from(b"key".to_vec()),
            Bytes::from(b"value".to_vec()),
        )]));
        let (key, LhsValue::Bytes(value)) = map.iter().next().unwrap() else {
            unreachable!();
        };
        for json in [r#"{"new":"entry"}"#, r#"[["new","entry"]]"#] {
            let mut borrowed = map.as_ref().clone();
            borrowed
                .deserialize(&mut serde_json::Deserializer::from_str(json))
                .unwrap();
            assert_eq!(map.len(), 1);
            assert_eq!(borrowed.len(), 2);
            let (borrowed_key, borrowed_value) = borrowed.into_iter().next().unwrap();
            let Bytes::Borrowed(borrowed_key) = borrowed_key else {
                panic!("existing key should be borrowed");
            };
            let LhsValue::Bytes(Bytes::Borrowed(borrowed_value)) = borrowed_value else {
                panic!("existing value should be borrowed");
            };
            assert!(std::ptr::eq(borrowed_key, key));
            assert!(std::ptr::eq(borrowed_value, value.as_ref()));
        }
    }

    #[test]
    fn test_deserialize_borrows_keys() {
        for json in [r#"{"key":42}"#, r#"[["key",42]]"#] {
            let mut map = Map::new(Type::Int);
            map.deserialize(&mut serde_json::Deserializer::from_str(json))
                .unwrap();
            assert!(matches!(
                map.clone().into_iter().next(),
                Some((Bytes::Borrowed(b"key"), LhsValue::Int(42)))
            ));
            assert!(matches!(
                map.as_ref().into_owned().into_iter().next(),
                Some((Bytes::Owned(_), LhsValue::Int(42)))
            ));
            assert!(matches!(
                map.into_owned().into_iter().next(),
                Some((Bytes::Owned(_), LhsValue::Int(42)))
            ));
        }
    }

    #[test]
    fn test_mixed_key_ownership() {
        let mut map =
            TypedMap::from_iter([(Bytes::Borrowed(b"z"), 1), (Bytes::from(b"a".to_vec()), 2)]);
        map.insert(Bytes::from(b"z".to_vec()), 3);
        map.extend([(Bytes::Borrowed(b"a"), 4)]);
        let map = Map::from(map);
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(b"z"), Some(&LhsValue::Int(3)));
        assert_eq!(map.get(b"a"), Some(&LhsValue::Int(4)));
        assert_eq!(serde_json::to_string(&map).unwrap(), r#"{"z":3,"a":4}"#);
    }

    #[test]
    fn test_iteration_preserves_insertion_order() {
        let map = Map::try_from_iter(
            Type::Int,
            [("z", 1), ("a", 2), ("m", 3), ("z", 4)]
                .map(|(key, value)| Ok::<_, TypeMismatchError>((key.into(), value))),
        )
        .unwrap();
        let expected_keys = [b"z".as_slice(), b"a", b"m"];
        for map in [
            map.clone(),
            map.as_ref(),
            map.clone().into_owned(),
            map.as_ref().into_owned(),
        ] {
            assert_eq!(
                map.iter().map(|(key, _)| key).collect::<Vec<_>>(),
                expected_keys
            );
            assert_eq!(
                map.clone()
                    .into_iter()
                    .map(|(key, _)| key)
                    .collect::<Vec<_>>(),
                expected_keys.map(Bytes::Borrowed)
            );
            assert_eq!(
                map.into_values().collect::<Vec<_>>(),
                [LhsValue::Int(4), LhsValue::Int(2), LhsValue::Int(3)]
            );
        }
    }

    #[test]
    fn test_deserialize_preserves_insertion_order() {
        let original = Map::from(TypedMap::from_iter([("z".into(), 1), ("a".into(), 2)]));
        for json in [r#"{"m":3,"z":4}"#, r#"[["m",3],["z",4]]"#] {
            let mut map = original.as_ref();
            map.deserialize(&mut serde_json::Deserializer::from_str(json))
                .unwrap();
            assert_eq!(
                serde_json::to_string(&map).unwrap(),
                r#"{"z":4,"a":2,"m":3}"#
            );
        }
    }

    #[test]
    fn test_hash_ignores_insertion_order() {
        let first = Map::from(TypedMap::from_iter([("z".into(), 1), ("a".into(), 2)]));
        let second = Map::from(TypedMap::from_iter([("a".into(), 2), ("z".into(), 1)]));
        assert_eq!(first, second);
        let hasher = RandomState::default();
        assert_eq!(hasher.hash_one(&first), hasher.hash_one(&second));
        assert_eq!(hasher.hash_one(&first), hasher.hash_one(first.as_ref()));
        assert_eq!(
            hasher.hash_one(&first),
            hasher.hash_one(first.as_ref().into_owned())
        );
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
