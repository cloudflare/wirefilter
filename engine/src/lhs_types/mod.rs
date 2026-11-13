//! Values stored by execution contexts and returned by value expressions.

mod array;
mod bytes;
mod map;

pub use self::array::{Array, ArrayIntoIter, ArrayIter, TypedArray};
pub use self::bytes::Bytes;
pub use self::map::{Map, MapIter, MapValuesIntoIter, TypedMap};
use crate::scheme::{FieldIndex, IndexAccessError};
use crate::strict_partial_ord::StrictPartialOrd;
use crate::types::{
    ExpectedType, GetType, LiteralValue, Type, TypeMismatchError, declare_types,
    specialized_get_type, specialized_try_from,
};
use crate::values::{FieldValueType, IntoLhsValue, ReadValue, Value, ValueError, ValuePredicate};
#[cfg(feature = "get-size2")]
use get_size2::{GetSize, GetSizeTracker};
use serde::de::{DeserializeSeed, Deserializer};
use serde::{Deserialize, Serialize, Serializer};
use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

macro_rules! declare_lhs_value {
    ($($(# $attrs:tt)* $name:ident $([$val_ty:ty])? ( $(# $lhs_attrs:tt)* $lhs_ty:ty | $literal_ty:ty | $literal_set_ty:ty ) , )*) => {
        declare_types! {
            /// An LHS value provided for filter execution.
            ///
            /// These are passed to the [`crate::ExecutionContext`]
            /// and are used by [`crate::Filter`] for execution and comparisons.
            #[derive(PartialEq, Eq, Clone, Deserialize, Hash)]
            #[serde(untagged)]
            enum LhsValue<'a> {
                $($(# $attrs)* $(# $lhs_attrs)* $name($lhs_ty),)*
            }
        }

        $(impl<'a> TryFrom<LhsValue<'a>> for $lhs_ty {
            type Error = TypeMismatchError;

            fn try_from(value: LhsValue<'a>) -> Result<$lhs_ty, TypeMismatchError> {
                match value {
                    LhsValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

        $(impl<'a> TryFrom<&'a LhsValue<'a>> for &'a $lhs_ty {
            type Error = TypeMismatchError;

            fn try_from(value: &'a LhsValue<'a>) -> Result<&'a $lhs_ty, TypeMismatchError> {
                match value {
                    LhsValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

        impl<'a> PartialOrd<LiteralValue> for LhsValue<'a> {
            fn partial_cmp(&self, other: &LiteralValue) -> Option<Ordering> {
                match (self, other) {
                    $((LhsValue::$name(lhs), LiteralValue::$name(rhs)) => {
                        lhs.strict_partial_cmp(rhs)
                    },)*
                    _ => None,
                }
            }
        }

    };
}

crate::types::with_value_types!(declare_lhs_value);

impl PartialEq<&LhsValue<'_>> for LhsValue<'_> {
    fn eq(&self, other: &&LhsValue<'_>) -> bool {
        self.eq(*other)
    }
}

impl StrictPartialOrd<LiteralValue> for LhsValue<'_> {}

impl PartialEq<LiteralValue> for LhsValue<'_> {
    fn eq(&self, other: &LiteralValue) -> bool {
        self.strict_partial_cmp(other) == Some(Ordering::Equal)
    }
}

mod private {
    use crate::Bytes;
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    pub trait SealedIntoValue {}

    impl SealedIntoValue for bool {}

    impl SealedIntoValue for i8 {}
    impl SealedIntoValue for u8 {}
    impl SealedIntoValue for i16 {}
    impl SealedIntoValue for u16 {}
    impl SealedIntoValue for i32 {}
    impl SealedIntoValue for u32 {}
    impl SealedIntoValue for i64 {}

    impl SealedIntoValue for IpAddr {}
    impl SealedIntoValue for Ipv4Addr {}
    impl SealedIntoValue for Ipv6Addr {}

    impl<'a, T> SealedIntoValue for T where Bytes<'a>: From<T> {}
}

/// Converts a value into an `LhsValue`.
/// It is a stronger version of `Into<LhsValue<'_>>` in that
/// any value of the input type will *always* convert to the
/// same statically known `LhsValue` variant.
pub trait IntoValue<'a>: private::SealedIntoValue {
    const TYPE: Type;

    fn into_value(self) -> LhsValue<'a>;
}

impl<'a> IntoValue<'a> for bool {
    const TYPE: Type = Type::Bool;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bool(self)
    }
}

impl<'a> IntoValue<'a> for i64 {
    const TYPE: Type = Type::Int;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Int(self)
    }
}

impl<'a> IntoValue<'a> for i32 {
    const TYPE: Type = Type::Int;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Int(i64::from(self))
    }
}

impl<'a> IntoValue<'a> for i16 {
    const TYPE: Type = Type::Int;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Int(i64::from(self))
    }
}

impl<'a> IntoValue<'a> for u16 {
    const TYPE: Type = Type::Int;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Int(i64::from(self))
    }
}

impl<'a> IntoValue<'a> for i8 {
    const TYPE: Type = Type::Int;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Int(i64::from(self))
    }
}

impl<'a> IntoValue<'a> for u8 {
    const TYPE: Type = Type::Int;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Int(i64::from(self))
    }
}

impl<'a> IntoValue<'a> for IpAddr {
    const TYPE: Type = Type::Ip;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Ip(self)
    }
}

impl<'a> IntoValue<'a> for Ipv4Addr {
    const TYPE: Type = Type::Ip;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Ip(IpAddr::V4(self))
    }
}

impl<'a> IntoValue<'a> for Ipv6Addr {
    const TYPE: Type = Type::Ip;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Ip(IpAddr::V6(self))
    }
}

impl<'a, T> IntoValue<'a> for T
where
    Bytes<'a>: From<T>,
{
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Bytes::from(self))
    }
}

impl<'a, T: IntoValue<'a>> From<T> for LhsValue<'a> {
    #[inline]
    fn from(value: T) -> Self {
        value.into_value()
    }
}

// Array cannot implement `IntoValue` as the
// underlying element type is not statically
// known.
impl<'a> From<Array<'a>> for LhsValue<'a> {
    #[inline]
    fn from(value: Array<'a>) -> LhsValue<'a> {
        LhsValue::Array(value)
    }
}

// Map cannot implement `IntoValue` as the
// underlying element type is not statically
// known.
impl<'a> From<Map<'a>> for LhsValue<'a> {
    #[inline]
    fn from(value: Map<'a>) -> LhsValue<'a> {
        LhsValue::Map(value)
    }
}

impl<'a> TryFrom<&'a LhsValue<'a>> for &'a [u8] {
    type Error = TypeMismatchError;

    fn try_from(value: &'a LhsValue<'_>) -> Result<Self, TypeMismatchError> {
        match value {
            LhsValue::Bytes(value) => Ok(value),
            _ => Err(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: value.get_type(),
            }),
        }
    }
}

impl<'a> From<&'a LiteralValue> for LhsValue<'a> {
    fn from(literal: &'a LiteralValue) -> Self {
        match literal {
            LiteralValue::Ip(ip) => LhsValue::Ip(*ip),
            LiteralValue::Bytes(bytes) => LhsValue::Bytes(Bytes::Borrowed(bytes)),
            LiteralValue::Int(integer) => LhsValue::Int(*integer),
            LiteralValue::Bool(b) => match *b {},
            LiteralValue::Array(a) => match *a {},
            LiteralValue::Map(m) => match *m {},
        }
    }
}

impl From<LiteralValue> for LhsValue<'_> {
    fn from(literal: LiteralValue) -> Self {
        match literal {
            LiteralValue::Ip(ip) => LhsValue::Ip(ip),
            LiteralValue::Bytes(bytes) => LhsValue::Bytes(Bytes::Owned(bytes.into())),
            LiteralValue::Int(integer) => LhsValue::Int(integer),
            LiteralValue::Bool(b) => match b {},
            LiteralValue::Array(a) => match a {},
            LiteralValue::Map(m) => match m {},
        }
    }
}

impl<'a> LhsValue<'a> {
    /// Converts a reference to an LhsValue to an LhsValue with an internal
    /// references
    pub fn as_ref(&'a self) -> Self {
        match self {
            LhsValue::Ip(ip) => LhsValue::Ip(*ip),
            LhsValue::Bytes(bytes) => LhsValue::Bytes(Bytes::Borrowed(bytes)),
            LhsValue::Int(integer) => LhsValue::Int(*integer),
            LhsValue::Bool(b) => LhsValue::Bool(*b),
            LhsValue::Array(a) => LhsValue::Array(a.as_ref()),
            LhsValue::Map(m) => LhsValue::Map(m.as_ref()),
        }
    }

    /// Converts an `LhsValue` with borrowed data to a fully owned `LhsValue`.
    pub fn into_owned(self) -> LhsValue<'static> {
        match self {
            LhsValue::Ip(ip) => LhsValue::Ip(ip),
            LhsValue::Bytes(bytes) => LhsValue::Bytes(Bytes::Owned(bytes.into_owned())),
            LhsValue::Int(i) => LhsValue::Int(i),
            LhsValue::Bool(b) => LhsValue::Bool(b),
            LhsValue::Array(arr) => LhsValue::Array(arr.into_owned()),
            LhsValue::Map(map) => LhsValue::Map(map.into_owned()),
        }
    }

    /// Retrieve an element from an LhsValue given a path item and a specified
    /// type.
    /// Returns a TypeMismatchError error if current type does not support it
    /// nested element.
    ///
    /// Both LhsValue::Array and LhsValue::Map support nested elements.
    pub(crate) fn get(
        &'a self,
        item: &FieldIndex,
    ) -> Result<Option<&'a LhsValue<'a>>, IndexAccessError> {
        match (self, item) {
            (LhsValue::Array(arr), FieldIndex::ArrayIndex(idx)) => Ok(arr.get(*idx as usize)),
            (_, FieldIndex::ArrayIndex(_)) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
            (LhsValue::Map(map), FieldIndex::MapKey(key)) => Ok(map.get(key.as_bytes())),
            (_, FieldIndex::MapKey(_)) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
            (_, FieldIndex::MapEach) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
        }
    }

    #[inline]
    pub(crate) fn get_nested(&'a self, indexes: &[FieldIndex]) -> Option<&'a LhsValue<'a>> {
        indexes
            .iter()
            .try_fold(self, |value, idx| value.get(idx).unwrap())
    }

    pub(crate) fn extract(
        self,
        item: &FieldIndex,
    ) -> Result<Option<LhsValue<'a>>, IndexAccessError> {
        match item {
            FieldIndex::ArrayIndex(idx) => match self {
                LhsValue::Array(arr) => Ok(arr.extract(*idx as usize)),
                _ => Err(IndexAccessError {
                    index: item.clone(),
                    actual: self.get_type(),
                }),
            },
            FieldIndex::MapKey(key) => match self {
                LhsValue::Map(map) => Ok(map.extract(key.as_bytes())),
                _ => Err(IndexAccessError {
                    index: item.clone(),
                    actual: self.get_type(),
                }),
            },
            FieldIndex::MapEach => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
        }
    }

    #[inline]
    pub(crate) fn extract_nested(self, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        indexes
            .iter()
            .try_fold(self, |value, idx| value.extract(idx).unwrap())
    }

    /// Returns an iterator over the Map or Array
    pub(crate) fn iter(&'a self) -> Option<Iter<'a>> {
        match self {
            LhsValue::Array(array) => Some(Iter::IterArray(array.iter())),
            LhsValue::Map(map) => Some(Iter::IterMap(map.iter())),
            _ => None,
        }
    }
}

impl Serialize for LhsValue<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            LhsValue::Ip(ip) => ip.serialize(serializer),
            LhsValue::Bytes(bytes) => {
                if let Ok(s) = std::str::from_utf8(bytes) {
                    serializer.serialize_str(s)
                } else {
                    serializer.serialize_bytes(bytes)
                }
            }
            LhsValue::Int(num) => num.serialize(serializer),
            LhsValue::Bool(b) => b.serialize(serializer),
            LhsValue::Array(arr) => arr.serialize(serializer),
            LhsValue::Map(map) => map.serialize(serializer),
        }
    }
}

pub(crate) struct LhsValueSeed<'a>(pub &'a Type);

impl<'de> DeserializeSeed<'de> for LhsValueSeed<'_> {
    type Value = LhsValue<'de>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        match self.0 {
            Type::Ip => Ok(LhsValue::Ip(std::net::IpAddr::deserialize(deserializer)?)),
            Type::Int => Ok(LhsValue::Int(i64::deserialize(deserializer)?)),
            Type::Bool => Ok(LhsValue::Bool(bool::deserialize(deserializer)?)),
            Type::Bytes => Ok(LhsValue::Bytes(Bytes::deserialize(deserializer)?)),
            Type::Array(ty) => Ok(LhsValue::Array({
                let mut arr = Array::new(*ty);
                arr.deserialize(deserializer)?;
                arr
            })),
            Type::Map(ty) => Ok(LhsValue::Map({
                let mut map = Map::new(*ty);
                map.deserialize(deserializer)?;
                map
            })),
        }
    }
}

pub enum IntoIter<'a> {
    IntoArray(ArrayIntoIter<'a>),
    IntoMap(MapValuesIntoIter<'a>),
}

impl<'a> Iterator for IntoIter<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        match self {
            IntoIter::IntoArray(array) => array.next(),
            IntoIter::IntoMap(map) => map.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for IntoIter<'_> {
    fn len(&self) -> usize {
        match self {
            IntoIter::IntoArray(array) => array.len(),
            IntoIter::IntoMap(map) => map.len(),
        }
    }
}

impl<'a> IntoIterator for LhsValue<'a> {
    type IntoIter = IntoIter<'a>;
    type Item = LhsValue<'a>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            LhsValue::Array(array) => IntoIter::IntoArray(array.into_iter()),
            LhsValue::Map(map) => IntoIter::IntoMap(map.into_values()),
            _ => unreachable!(),
        }
    }
}

pub(crate) enum Iter<'a> {
    IterArray(ArrayIter<'a, 'a>),
    IterMap(MapIter<'a, 'a>),
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a LhsValue<'a>;

    fn next(&mut self) -> Option<&'a LhsValue<'a>> {
        match self {
            Iter::IterArray(array) => array.next(),
            Iter::IterMap(map) => map.next().map(|(_, v)| v),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for Iter<'_> {
    fn len(&self) -> usize {
        match self {
            Iter::IterArray(array) => array.len(),
            Iter::IterMap(map) => map.len(),
        }
    }
}

pub struct AsRefIterator<'a, T: Iterator<Item = &'a LhsValue<'a>>>(T);

impl<'a, T: Iterator<Item = &'a LhsValue<'a>>> AsRefIterator<'a, T> {
    pub fn new(iter: T) -> Self {
        Self(iter)
    }
}

impl<'a, T: Iterator<Item = &'a LhsValue<'a>>> Iterator for AsRefIterator<'a, T> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(LhsValue::as_ref)
    }
}

impl<'a, T: ExactSizeIterator<Item = &'a LhsValue<'a>>> ExactSizeIterator for AsRefIterator<'a, T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

pub(crate) fn append_stored_lhs_at<'a>(
    mut value: LhsValue<'a>,
    mut indexes: &[FieldIndex],
    output: &mut Vec<LhsValue<'a>>,
) {
    while let Some((index, rest)) = indexes.split_first() {
        if *index == FieldIndex::MapEach {
            let values = value.into_iter();
            if rest.is_empty() {
                output.extend(values);
            } else {
                for value in values {
                    append_stored_lhs_at(value, rest, output);
                }
            }
            return;
        }
        let Some(selected) = value.extract(index).expect("invalid value selection path") else {
            return;
        };
        value = selected;
        indexes = rest;
    }
    output.push(value);
}

/// A stored field whose logical type is supplied by the scheme.
///
/// Unlike a static [`super::values::ValueType`], this describes an entire field,
/// including arbitrary collection nesting, rather than a statically typed container element.
/// Contexts must check values against the declared type when inserting them, as
/// [`crate::ExecutionContext::set_field_value`] does. Startup validation cannot
/// infer the variant returned by an arbitrary getter of [`LhsValue`].
pub struct LhsValueType;

impl FieldValueType for LhsValueType {
    type Path = Box<[FieldIndex]>;

    const DIRECT_COLLECTION_COMPARISON: bool = true;
    const STATIC_TYPE: Option<Type> = None;

    fn compile_field_path(
        mut field_type: Type,
        path: Vec<FieldIndex>,
        input_type: Type,
    ) -> Result<Self::Path, ValueError> {
        for step in &path {
            field_type = match (field_type, step) {
                (Type::Array(child), FieldIndex::ArrayIndex(_) | FieldIndex::MapEach)
                | (Type::Map(child), FieldIndex::MapKey(_) | FieldIndex::MapEach) => child.into(),
                _ => return Err(ValueError("index does not match the declared field type")),
            };
        }
        if field_type != input_type {
            return Err(ValueError(
                "predicate input type differs from selected value",
            ));
        }
        Ok(path.into_boxed_slice())
    }
}

/// Engine reader borrowing existing Wirefilter values and their containers.
pub struct LhsValueRead;

impl LhsValueRead {
    /// Compare a selected value while retaining the caller's value ownership.
    pub(crate) fn compare_one<P: ValuePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &[FieldIndex],
        predicate: &P,
    ) -> Option<bool> {
        value.get_nested(path).map(|value| predicate.lhs(value))
    }

    /// Compare selections from a possibly nested path.
    pub(crate) fn compare_vec<P: ValuePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &[FieldIndex],
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        compare_each(value, path, predicate, output);
    }

    /// Compare each child of the collection selected by a concrete prefix.
    /// Keeping the final iteration implicit avoids retaining another path entry.
    pub(crate) fn compare_items<P: ValuePredicate + ?Sized>(
        value: &LhsValue<'_>,
        prefix: &[FieldIndex],
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        if let Some(value) = value.get_nested(prefix) {
            compare_each(value, &[FieldIndex::MapEach], predicate, output);
        }
    }
}

impl Value for LhsValue<'_> {
    type Read = LhsValueRead;
    type ValueType = LhsValueType;
}

impl<'a, 'data: 'a> IntoLhsValue<'a> for LhsValue<'data> {
    const MATERIALIZES_COLLECTIONS: bool = false;

    #[inline]
    fn into_lhs(self) -> LhsValue<'a> {
        self
    }

    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        append_stored_lhs_at(self, indexes, output);
    }
}

impl ReadValue<LhsValue<'_>, LhsValueType> for LhsValueRead {
    const MATERIALIZES_COLLECTIONS: bool = false;

    #[inline]
    fn to_lhs<'a>(value: &'a LhsValue<'_>) -> LhsValue<'a> {
        value.as_ref()
    }

    #[inline]
    fn to_lhs_at<'a>(value: &'a LhsValue<'_>, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        value.get_nested(indexes).map(LhsValue::as_ref)
    }

    #[inline]
    fn append_lhs_at<'a>(
        value: &'a LhsValue<'_>,
        indexes: &[FieldIndex],
        output: &mut Vec<LhsValue<'a>>,
    ) {
        append_stored_lhs_at(value.as_ref(), indexes, output);
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &Box<[FieldIndex]>,
        predicate: &P,
    ) -> Option<bool> {
        Self::compare_one(value, path, predicate)
    }

    #[inline]
    fn compare_vec<P: ValuePredicate + ?Sized>(
        value: &LhsValue<'_>,
        path: &Box<[FieldIndex]>,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        Self::compare_vec(value, path, predicate, output);
    }
}

fn compare_each<'a, P: ValuePredicate + ?Sized>(
    mut value: &'a LhsValue<'a>,
    mut path: &[FieldIndex],
    predicate: &P,
    output: &mut TypedArray<'static, bool>,
) {
    // Follow concrete indices while reading values, without first searching for
    // [*]. Only collection iteration recurses; concrete indices add no calls.
    while let Some((index, rest)) = path.split_first() {
        if *index == FieldIndex::MapEach {
            let children = value.iter().expect("[*] requires a collection");
            if rest.is_empty() {
                if output.is_empty() {
                    *output = TypedArray::with_capacity(children.size_hint().0);
                }
                for child in children {
                    output.push(predicate.lhs(child));
                }
            } else {
                for child in children {
                    compare_each(child, rest, predicate, output);
                }
            }
            return;
        }
        let Some(child) = value.get(index).unwrap() else {
            return;
        };
        value = child;
        path = rest;
    }
    output.push(predicate.lhs(value));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn validates_paths_against_the_scheme_type() {
        let root = Type::map(Type::array(Type::Int));
        let path = vec![FieldIndex::MapKey("values".into()), FieldIndex::MapEach];
        assert_eq!(
            LhsValueType::compile_field_path(root, path.clone(), Type::Int).unwrap(),
            path.into_boxed_slice(),
        );
        assert!(LhsValueType::compile_field_path(root, vec![], root).is_ok());
        assert!(LhsValueType::compile_field_path(root, vec![], Type::Int).is_err());
        assert!(
            LhsValueType::compile_field_path(
                root,
                vec![FieldIndex::ArrayIndex(0)],
                Type::array(Type::Int),
            )
            .is_err()
        );
        assert!(
            LhsValueType::compile_field_path(Type::Int, vec![FieldIndex::MapEach], Type::Int,)
                .is_err()
        );
        assert!(
            LhsValueType::compile_field_path(
                Type::array(Type::Int),
                vec![FieldIndex::MapKey("values".into())],
                Type::Int,
            )
            .is_err()
        );
    }
}

#[cfg(feature = "get-size2")]
impl GetSize for LhsValue<'_> {
    fn get_heap_size_with_tracker<T: GetSizeTracker>(&self, tracker: T) -> (usize, T) {
        match self {
            Self::Bool(_) | Self::Int(_) | Self::Ip(_) => (0, tracker),
            Self::Bytes(value) => value.get_heap_size_with_tracker(tracker),
            Self::Array(value) => value.get_heap_size_with_tracker(tracker),
            Self::Map(value) => value.get_heap_size_with_tracker(tracker),
        }
    }
}

#[test]
fn test_lhs_value_deserialize() {
    use std::str::FromStr;

    let ipv4: LhsValue<'_> = serde_json::from_str("\"127.0.0.1\"").unwrap();
    assert_eq!(ipv4, LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap()));

    let ipv6: LhsValue<'_> = serde_json::from_str("\"::1\"").unwrap();
    assert_eq!(ipv6, LhsValue::Ip(IpAddr::from_str("::1").unwrap()));

    let bytes: LhsValue<'_> = serde_json::from_str("\"a JSON string with unicode ❤\"").unwrap();
    assert_eq!(
        bytes,
        LhsValue::from(&b"a JSON string with unicode \xE2\x9D\xA4"[..])
    );

    let bytes =
        serde_json::from_str::<LhsValue<'_>>("\"a JSON string with escaped-unicode \\u2764\"")
            .unwrap();
    assert_eq!(
        bytes,
        LhsValue::from(&b"a JSON string with escaped-unicode \xE2\x9D\xA4"[..])
    );

    let bytes: LhsValue<'_> = serde_json::from_str("\"1337\"").unwrap();
    assert_eq!(bytes, LhsValue::from(&b"1337"[..]));

    let integer: LhsValue<'_> = serde_json::from_str("1337").unwrap();
    assert_eq!(integer, LhsValue::Int(1337));

    let b: LhsValue<'_> = serde_json::from_str("false").unwrap();
    assert_eq!(b, LhsValue::Bool(false));
}

#[test]
fn test_size_of_lhs_value() {
    assert_eq!(std::mem::size_of::<LhsValue<'_>>(), 48);
}

#[cfg(feature = "get-size2")]
#[test]
fn test_lhs_value_get_size() {
    let stack_size = std::mem::size_of::<LhsValue<'static>>();

    assert_eq!(LhsValue::Bool(false).get_size(), stack_size);
    assert_eq!(LhsValue::Int(42).get_size(), stack_size);
    assert_eq!(
        LhsValue::Ip(IpAddr::V4(Ipv4Addr::LOCALHOST)).get_size(),
        stack_size
    );

    let borrowed_bytes = LhsValue::Bytes(Bytes::Borrowed(b"borrowed"));
    assert_eq!(borrowed_bytes.get_size(), stack_size);

    let owned_bytes = LhsValue::Bytes(Bytes::Owned(Box::from(&b"owned"[..])));
    assert_eq!(owned_bytes.get_size(), stack_size + b"owned".len());
}

#[cfg(feature = "get-size2")]
#[test]
fn test_array_lhs_value_get_size() {
    let stack_size = std::mem::size_of::<LhsValue<'static>>();

    let mut borrowed_values = Vec::with_capacity(4);
    borrowed_values.push(LhsValue::Bytes(Bytes::Borrowed(b"borrowed")));
    let borrowed_values_capacity = borrowed_values.capacity();
    let owned_array_of_borrowed = Array::try_from_vec(Type::Bytes, borrowed_values).unwrap();
    assert_eq!(
        LhsValue::Array(owned_array_of_borrowed.as_ref()).get_size(),
        stack_size
    );
    assert_eq!(
        LhsValue::Array(owned_array_of_borrowed).get_size(),
        stack_size + borrowed_values_capacity * stack_size
    );

    let mut owned_values = Vec::with_capacity(4);
    owned_values.push(LhsValue::Bytes(Bytes::Owned(Box::from(&b"owned"[..]))));
    let owned_values_capacity = owned_values.capacity();
    let owned_array_of_owned = Array::try_from_vec(Type::Bytes, owned_values).unwrap();
    assert_eq!(
        LhsValue::Array(owned_array_of_owned.as_ref()).get_size(),
        stack_size
    );
    assert_eq!(
        LhsValue::Array(owned_array_of_owned).get_size(),
        stack_size + owned_values_capacity * stack_size + b"owned".len()
    );
}

#[cfg(feature = "get-size2")]
#[test]
fn test_map_lhs_value_get_size() {
    let stack_size = std::mem::size_of::<LhsValue<'static>>();

    let owned_map_of_borrowed = Map::try_from_iter(
        Type::Bytes,
        [Ok::<_, TypeMismatchError>((
            Box::from(b"key".as_slice()),
            Bytes::Borrowed(b"borrowed"),
        ))],
    )
    .unwrap();
    assert_eq!(
        LhsValue::Map(owned_map_of_borrowed.as_ref()).get_size(),
        stack_size
    );
    assert_eq!(
        LhsValue::Map(owned_map_of_borrowed).get_size(),
        stack_size + std::mem::size_of::<Box<[u8]>>() + b"key".len() + stack_size
    );

    let owned_map_of_owned = Map::try_from_iter(
        Type::Bytes,
        [Ok::<_, TypeMismatchError>((
            Box::from(b"key".as_slice()),
            Bytes::Owned(Box::from(&b"owned"[..])),
        ))],
    )
    .unwrap();
    assert_eq!(
        LhsValue::Map(owned_map_of_owned.as_ref()).get_size(),
        stack_size
    );
    assert_eq!(
        LhsValue::Map(owned_map_of_owned).get_size(),
        stack_size + std::mem::size_of::<Box<[u8]>>() + b"key".len() + stack_size + b"owned".len()
    );
}
