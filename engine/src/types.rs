use crate::{
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    lhs_types::{Array, ArrayIterator, Map, MapIter, MapValuesIntoIter},
    rhs_types::{Bytes, IpRange, UninhabitedArray, UninhabitedBool, UninhabitedMap},
    scheme::{FieldIndex, IndexAccessError},
    strict_partial_ord::StrictPartialOrd,
};
use serde::de::{DeserializeSeed, Deserializer};
use serde::{Deserialize, Serialize, Serializer};
use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::HashSet,
    convert::TryFrom,
    fmt::{self, Debug, Formatter},
    iter::once,
    net::IpAddr,
    ops::RangeInclusive,
};
use thiserror::Error;

fn lex_rhs_values<'i, T: Lex<'i>>(input: &'i str) -> LexResult<'i, Vec<T>> {
    let mut input = expect(input, "{")?;
    let mut res = Vec::new();
    loop {
        input = skip_space(input);
        if let Ok(rest) = expect(input, "}") {
            input = rest;
            return Ok((res, input));
        } else {
            let (item, rest) = T::lex(input)?;
            res.push(item);
            input = rest;
        }
    }
}

/// An enum describing the expected type when a
/// TypeMismatchError occurs
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpectedType {
    /// Fully identified expected type
    Type(Type),
    /// Loosely identified array type
    /// Usefull when expecting an array without
    /// knowing of which specific value type
    Array,
    /// Loosely identified map type
    /// Usefull when expecting a map without
    /// knowing of which specific value type
    Map,
}

impl From<Type> for ExpectedType {
    fn from(ty: Type) -> Self {
        ExpectedType::Type(ty)
    }
}

type ExpectedTypeList = HashSet<ExpectedType>;

impl From<Type> for ExpectedTypeList {
    fn from(ty: Type) -> Self {
        once(ExpectedType::Type(ty)).collect()
    }
}

impl From<ExpectedType> for ExpectedTypeList {
    fn from(ty: ExpectedType) -> Self {
        once(ty).collect()
    }
}

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Error)]
#[error("expected value of type {expected:?}, but got {actual:?}")]
pub struct TypeMismatchError {
    /// Expected value type.
    pub expected: ExpectedTypeList,
    /// Provided value type.
    pub actual: Type,
}

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Error)]
pub enum SetValueError {
    #[error("{0}")]
    TypeMismatch(#[source] TypeMismatchError),
    #[error("{0}")]
    IndexAccess(#[source] IndexAccessError),
}

macro_rules! replace_underscore {
    ($name:ident ($val_ty:ty)) => {Type::$name(_)};
    ($name:ident) => {Type::$name};
}

macro_rules! specialized_get_type {
    (Array, $value:ident) => {
        $value.get_type()
    };
    (Map, $value:ident) => {
        $value.get_type()
    };
    ($name:ident, $value:ident) => {
        Type::$name
    };
}

macro_rules! specialized_try_from {
    (Array) => {
        ExpectedType::Array
    };
    (Map) => {
        ExpectedType::Map
    };
    ($name:ident) => {
        ExpectedType::Type(Type::$name)
    };
}

/// This macro generates `Type`, `LhsValue`, `RhsValue`, `RhsValues`.
///
/// Before the parenthesis is the variant for the `Type` enum (`Type::Ip`).
/// First argument is the corresponding `LhsValue` variant (`LhsValue::Ip(IpAddr)`).
/// Second argument is the corresponding `RhsValue` variant (`RhsValue::Ip(IpAddr)`).
/// Third argument is the corresponding `RhsValues` variant (`RhsValues::Ip(Vec<IpRange>)`) for the curly bracket syntax. eg `num in {1, 5}`
///
/// ```
/// declare_types! {
///     Ip(IpAddr | IpAddr | IpRange),
/// }
/// ```
macro_rules! declare_types {
    // This is just to be used by the other arm.
    ($(# $attrs:tt)* enum $name:ident $(<$lt:tt>)* { $($(# $vattrs:tt)* $variant:ident ( $ty:ty ) , )* }) => {
        $(# $attrs)*
        #[repr(u8)]
        pub enum $name $(<$lt>)* {
            $($(# $vattrs)* $variant($ty),)*
        }

        impl $(<$lt>)* GetType for $name $(<$lt>)* {
            fn get_type(&self) -> Type {
                match self {
                    $($name::$variant(_value) => specialized_get_type!($variant, _value),)*
                }
            }
        }

        impl $(<$lt>)* Debug for $name $(<$lt>)* {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                match self {
                    $($name::$variant(inner) => Debug::fmt(inner, f),)*
                }
            }
        }
    };

    // This is the entry point for the macro.
    ($($(# $attrs:tt)* $name:ident $([$val_ty:ty])? ( $(# $lhs_attrs:tt)* $lhs_ty:ty | $rhs_ty:ty | $multi_rhs_ty:ty ) , )*) => {
        /// Enumeration of supported types for field values.
        #[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize, Hash)]
        pub enum Type {
            $($(# $attrs)* $name$(($val_ty))?,)*
        }

        declare_types! {
            /// An LHS value provided for filter execution.
            ///
            /// These are passed to the [execution context](::ExecutionContext)
            /// and are used by [filters](::Filter)
            /// for execution and comparisons.
            #[derive(PartialEq, Eq, Clone, Deserialize)]
            #[serde(untagged)]
            enum LhsValue<'a> {
                $($(# $attrs)* $(# $lhs_attrs)* $name($lhs_ty),)*
            }
        }

        $(impl<'a> From<$lhs_ty> for LhsValue<'a> {
            fn from(value: $lhs_ty) -> Self {
                LhsValue::$name(value)
            }
        })*

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

        declare_types! {
            /// An RHS value parsed from a filter string.
            #[derive(PartialEq, Eq, Clone, Hash, Serialize)]
            #[serde(untagged)]
            enum RhsValue {
                $($(# $attrs)* $name($rhs_ty),)*
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValue {
            fn lex_with(input: &str, ty: Type) -> LexResult<'_, Self> {
                Ok(match ty {
                    $(replace_underscore!($name $(($val_ty))?) => {
                        let (value, input) = <$rhs_ty>::lex(input)?;
                        (RhsValue::$name(value), input)
                    })*
                })
            }
        }

        impl<'a> PartialOrd<RhsValue> for LhsValue<'a> {
            fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
                match (self, other) {
                    $((LhsValue::$name(lhs), RhsValue::$name(rhs)) => {
                        lhs.strict_partial_cmp(rhs)
                    },)*
                    _ => None,
                }
            }
        }

        declare_types! {
            /// A typed group of a list of values.
            ///
            /// This is used for `field in { ... }` operation that allows
            /// only same-typed values in a list.
            #[derive(PartialEq, Eq, Clone, Hash, Serialize)]
            #[serde(untagged)]
            enum RhsValues {
                $($(# $attrs)* $name(Vec<$multi_rhs_ty>),)*
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValues {
            fn lex_with(input: &str, ty: Type) -> LexResult<'_, Self> {
                Ok(match ty {
                    $(replace_underscore!($name $(($val_ty))?) => {
                        let (value, input) = lex_rhs_values(input)?;
                        (RhsValues::$name(value), input)
                    })*
                })
            }
        }
    };
}

impl Type {
    /// Returns the inner type when available (e.g: for a Map)
    pub fn next(&self) -> Option<Type> {
        match self {
            Type::Array(ty) => Some(*ty.clone()),
            Type::Map(ty) => Some(*ty.clone()),
            _ => None,
        }
    }
}

/// Provides a way to get a [`Type`] of the implementor.
pub trait GetType {
    /// Returns a type.
    fn get_type(&self) -> Type;
}

impl GetType for Type {
    fn get_type(&self) -> Type {
        self.clone()
    }
}

impl<'a> StrictPartialOrd<RhsValue> for LhsValue<'a> {}

impl<'a> PartialEq<RhsValue> for LhsValue<'a> {
    fn eq(&self, other: &RhsValue) -> bool {
        self.strict_partial_cmp(other) == Some(Ordering::Equal)
    }
}

#[derive(Deserialize)]
#[serde(untagged)]
pub enum BytesOrString<'a> {
    BorrowedBytes(#[serde(borrow)] &'a [u8]),
    OwnedBytes(Vec<u8>),
    BorrowedString(#[serde(borrow)] &'a str),
    OwnedString(String),
}

impl<'a> BytesOrString<'a> {
    pub fn into_bytes(self) -> Cow<'a, [u8]> {
        match self {
            BytesOrString::BorrowedBytes(slice) => (*slice).into(),
            BytesOrString::OwnedBytes(vec) => vec.into(),
            BytesOrString::BorrowedString(str) => str.as_bytes().into(),
            BytesOrString::OwnedString(str) => str.into_bytes().into(),
        }
    }
}

// special case for simply passing bytes
impl<'a> From<&'a [u8]> for LhsValue<'a> {
    fn from(b: &'a [u8]) -> Self {
        LhsValue::Bytes(Cow::Borrowed(b))
    }
}

// special case for simply passing strings
impl<'a> From<&'a str> for LhsValue<'a> {
    fn from(s: &'a str) -> Self {
        s.as_bytes().into()
    }
}

impl<'a> TryFrom<&'a LhsValue<'a>> for &'a [u8] {
    type Error = TypeMismatchError;

    fn try_from(value: &'a LhsValue<'_>) -> Result<Self, TypeMismatchError> {
        match value {
            LhsValue::Bytes(value) => Ok(&*value),
            _ => Err(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: value.get_type(),
            }),
        }
    }
}

impl<'a> From<&'a RhsValue> for LhsValue<'a> {
    fn from(rhs_value: &'a RhsValue) -> Self {
        match rhs_value {
            RhsValue::Ip(ip) => LhsValue::Ip(*ip),
            RhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Borrowed(bytes)),
            RhsValue::Int(integer) => LhsValue::Int(*integer),
            RhsValue::Bool(b) => match *b {},
            RhsValue::Array(a) => match *a {},
            RhsValue::Map(m) => match *m {},
        }
    }
}

impl<'a> From<RhsValue> for LhsValue<'a> {
    fn from(rhs_value: RhsValue) -> Self {
        match rhs_value {
            RhsValue::Ip(ip) => LhsValue::Ip(ip),
            RhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Owned(bytes.into())),
            RhsValue::Int(integer) => LhsValue::Int(integer),
            RhsValue::Bool(b) => match b {},
            RhsValue::Array(a) => match a {},
            RhsValue::Map(m) => match m {},
        }
    }
}

impl<'a> LhsValue<'a> {
    /// Converts a reference to an LhsValue to an LhsValue with an internal
    /// references
    pub fn as_ref(&'a self) -> Self {
        match self {
            LhsValue::Ip(ip) => LhsValue::Ip(*ip),
            LhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Borrowed(bytes)),
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
            LhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Owned(bytes.into_owned())),
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
    pub fn get(&'a self, item: &FieldIndex) -> Result<Option<&'a LhsValue<'a>>, IndexAccessError> {
        match (self, item) {
            (LhsValue::Array(arr), FieldIndex::ArrayIndex(ref idx)) => Ok(arr.get(*idx as usize)),
            (_, FieldIndex::ArrayIndex(_)) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
            (LhsValue::Map(map), FieldIndex::MapKey(ref key)) => Ok(map.get(key.as_bytes())),
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

    /// Set an element in an LhsValue given a path item and a specified value.
    /// Returns a TypeMismatchError error if current type does not support
    /// nested element or if value type is invalid.
    /// Only LhsValyue::Map supports nested elements for now.
    pub fn set<V: Into<LhsValue<'a>>>(
        &mut self,
        item: FieldIndex,
        value: V,
    ) -> Result<(), SetValueError> {
        let value = value.into();
        match item {
            FieldIndex::ArrayIndex(idx) => match self {
                LhsValue::Array(ref mut arr) => arr
                    .insert(idx as usize, value)
                    .map_err(SetValueError::TypeMismatch),
                _ => Err(SetValueError::IndexAccess(IndexAccessError {
                    index: item,
                    actual: self.get_type(),
                })),
            },
            FieldIndex::MapKey(name) => match self {
                LhsValue::Map(ref mut map) => map
                    .insert(name.as_bytes(), value)
                    .map_err(SetValueError::TypeMismatch),
                _ => Err(SetValueError::IndexAccess(IndexAccessError {
                    index: FieldIndex::MapKey(name),
                    actual: self.get_type(),
                })),
            },
            FieldIndex::MapEach => Err(SetValueError::IndexAccess(IndexAccessError {
                index: item,
                actual: self.get_type(),
            })),
        }
    }

    /// Returns an iterator over the Map or Array
    pub fn iter(&'a self) -> Option<Iter<'a>> {
        match self {
            LhsValue::Array(array) => Some(Iter::IterArray(array.as_slice().iter())),
            LhsValue::Map(map) => Some(Iter::IterMap(map.iter())),
            _ => None,
        }
    }
}

impl<'a> Serialize for LhsValue<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self {
            LhsValue::Ip(ip) => ip.serialize(serializer),
            LhsValue::Bytes(bytes) => {
                if let Ok(s) = std::str::from_utf8(bytes) {
                    s.serialize(serializer)
                } else {
                    bytes.serialize(serializer)
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

impl<'de, 'a> DeserializeSeed<'de> for LhsValueSeed<'a> {
    type Value = LhsValue<'de>;

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        match self.0 {
            Type::Ip => Ok(LhsValue::Ip(std::net::IpAddr::deserialize(deserializer)?)),
            Type::Int => Ok(LhsValue::Int(i32::deserialize(deserializer)?)),
            Type::Bool => Ok(LhsValue::Bool(bool::deserialize(deserializer)?)),
            Type::Bytes => Ok(LhsValue::Bytes(
                BytesOrString::deserialize(deserializer)?.into_bytes(),
            )),
            Type::Array(ty) => Ok(LhsValue::Array({
                let mut arr = Array::new((**ty).clone());
                arr.deserialize(deserializer)?;
                arr
            })),
            Type::Map(ty) => Ok(LhsValue::Map({
                let mut map = Map::new((**ty).clone());
                map.deserialize(deserializer)?;
                map
            })),
        }
    }
}

pub enum IntoIter<'a> {
    IntoArray(ArrayIterator<'a>),
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
}

impl<'a> IntoIterator for LhsValue<'a> {
    type Item = LhsValue<'a>;
    type IntoIter = IntoIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            LhsValue::Array(array) => IntoIter::IntoArray(array.into_iter()),
            LhsValue::Map(map) => IntoIter::IntoMap(map.values_into_iter()),
            _ => unreachable!(),
        }
    }
}

pub enum Iter<'a> {
    IterArray(std::slice::Iter<'a, LhsValue<'a>>),
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
}

declare_types!(
    /// An IPv4 or IPv6 address.
    ///
    /// These are represented as a single type to allow interop comparisons.
    Ip(IpAddr | IpAddr | IpRange),

    /// A raw bytes or a string field.
    ///
    /// These are completely interchangeable in runtime and differ only in
    /// syntax representation, so we represent them as a single type.
    Bytes(#[serde(borrow)] Cow<'a, [u8]> | Bytes | Bytes),

    /// A 32-bit integer number.
    Int(i32 | i32 | RangeInclusive<i32>),

    /// A boolean.
    Bool(bool | UninhabitedBool | UninhabitedBool),

    /// An Array of [`Type`].
    Array[Box<Type>](#[serde(skip_deserializing)] Array<'a> | UninhabitedArray | UninhabitedArray),

    /// A Map of string to [`Type`].
    Map[Box<Type>](#[serde(skip_deserializing)] Map<'a> | UninhabitedMap | UninhabitedMap),
);

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
