use crate::{
    lex::{Lex, LexResult, LexWith, expect, skip_space},
    lhs_types::{Array, ArrayIterator, Map, MapIter, MapValuesIntoIter},
    rhs_types::{Bytes, IntRange, IpRange, UninhabitedArray, UninhabitedBool, UninhabitedMap},
    scheme::{FieldIndex, IndexAccessError},
    strict_partial_ord::StrictPartialOrd,
};
use serde::de::{DeserializeSeed, Deserializer};
use serde::{Deserialize, Serialize, Serializer};
use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::BTreeSet,
    convert::TryFrom,
    fmt::{self, Debug, Formatter},
    iter::once,
    net::{IpAddr, Ipv4Addr, Ipv6Addr},
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
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExpectedType {
    /// Fully identified expected type
    Type(Type),
    /// Loosely identified array type
    /// Useful when expecting an array without
    /// knowing of which specific value type
    Array,
    /// Loosely identified map type
    /// Useful when expecting a map without
    /// knowing of which specific value type
    Map,
}

impl From<Type> for ExpectedType {
    fn from(ty: Type) -> Self {
        ExpectedType::Type(ty)
    }
}

impl std::fmt::Display for ExpectedType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ExpectedType::Array => write!(f, "Array<_>"),
            ExpectedType::Map => write!(f, "Map<_>"),
            ExpectedType::Type(ty) => write!(f, "{ty}"),
        }
    }
}

/// A list of expected types.
#[derive(Default, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExpectedTypeList(BTreeSet<ExpectedType>);

impl ExpectedTypeList {
    /// Insert an expected type in the list.
    pub fn insert(&mut self, ty: impl Into<ExpectedType>) {
        self.0.insert(ty.into());
    }
}

impl fmt::Debug for ExpectedTypeList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl From<Type> for ExpectedTypeList {
    #[inline]
    fn from(ty: Type) -> Self {
        Self(once(ExpectedType::Type(ty)).collect())
    }
}

impl From<ExpectedType> for ExpectedTypeList {
    #[inline]
    fn from(ty: ExpectedType) -> Self {
        Self(once(ty).collect())
    }
}

impl<T: Iterator<Item = ExpectedType>> From<T> for ExpectedTypeList {
    #[inline]
    fn from(tys: T) -> Self {
        Self(tys.collect())
    }
}

impl std::fmt::Display for ExpectedTypeList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.len() {
            0 => unreachable!(),
            1 => write!(f, "{}", self.0.first().unwrap()),
            2 => write!(
                f,
                "{} or {}",
                self.0.first().unwrap(),
                self.0.last().unwrap()
            ),
            _ => {
                let mut iter = self.0.iter();
                let first = iter.next().unwrap();
                write!(f, "{{{first}")?;
                for expected_type in iter {
                    write!(f, ", {expected_type}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("expected value of type {expected}, but got {actual}")]
pub struct TypeMismatchError {
    /// Expected value type.
    pub expected: ExpectedTypeList,
    /// Provided value type.
    pub actual: Type,
}

macro_rules! replace_underscore {
    ($name:ident ($val_ty:ty)) => {
        Type::$name(_)
    };
    ($name:ident) => {
        Type::$name
    };
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

// This macro generates `Type`, `LhsValue`, `RhsValue`, `RhsValues`.
//
// Before the parenthesis is the variant for the `Type` enum (`Type::Ip`).
// First argument is the corresponding `LhsValue` variant (`LhsValue::Ip(IpAddr)`).
// Second argument is the corresponding `RhsValue` variant (`RhsValue::Ip(IpAddr)`).
// Third argument is the corresponding `RhsValues` variant (`RhsValues::Ip(Vec<IpRange>)`) for the curly bracket syntax. eg `num in {1, 5}`
//
// ```
// declare_types! {
//     Ip(IpAddr | IpAddr | IpRange),
// }
// ```
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
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Hash, PartialOrd, Ord)]
        pub enum Type {
            $($(# $attrs)* $name$(($val_ty))?,)*
        }

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

        $(impl<'a> TryFrom<RhsValue> for $rhs_ty {
            type Error = TypeMismatchError;

            fn try_from(value: RhsValue) -> Result<$rhs_ty, TypeMismatchError> {
                match value {
                    RhsValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

        $(impl<'a> TryFrom<&'a RhsValue> for &'a $rhs_ty {
            type Error = TypeMismatchError;

            fn try_from(value: &'a RhsValue) -> Result<&'a $rhs_ty, TypeMismatchError> {
                match value {
                    RhsValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

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

        impl From<RhsValue> for RhsValues {
            fn from(rhs: RhsValue) -> Self {
                match rhs {
                    $(RhsValue::$name(rhs) => {
                        #[allow(unreachable_code)]
                        RhsValues::$name(vec![rhs.into()])
                    })*
                }
            }
        }

        impl RhsValues {
            /// Appends a value to the back of the collection.
            pub fn push(&mut self, rhs: RhsValue) -> Result<(), TypeMismatchError> {
                match self {
                    $(RhsValues::$name(vec) => match rhs {
                        RhsValue::$name(rhs) => {
                            #[allow(unreachable_code)]
                            Ok(vec.push(rhs.into()))
                        }
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: rhs.get_type(),
                        }),
                    },)*
                }
            }

            /// Moves all the values of `other` into `self`, leaving `other` empty.
            pub fn append(&mut self, other: &mut Self) -> Result<(), TypeMismatchError> {
                match self {
                    $(RhsValues::$name(vec) => match other {
                        RhsValues::$name(other) => Ok(vec.append(other)),
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: other.get_type(),
                        }),
                    },)*
                }
            }

            /// Extends the collection with the values of another collection.
            pub fn extend(&mut self, other: Self) -> Result<(), TypeMismatchError> {
                match self {
                    $(RhsValues::$name(vec) => match other {
                        RhsValues::$name(other) => Ok(vec.extend(other)),
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: other.get_type(),
                        }),
                    },)*
                }
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
            Type::Array(ty) => Some((*ty).into()),
            Type::Map(ty) => Some((*ty).into()),
            _ => None,
        }
    }

    /// Creates a new array type.
    pub fn array(ty: impl Into<CompoundType>) -> Self {
        Self::Array(ty.into())
    }

    /// Creates a new map type.
    pub fn map(ty: impl Into<CompoundType>) -> Self {
        Self::Map(ty.into())
    }

    /// Deserializes a value based on its type.
    pub fn deserialize_value<'de, D>(&self, deserializer: D) -> Result<LhsValue<'de>, D::Error>
    where
        D: Deserializer<'de>,
    {
        LhsValueSeed(self).deserialize(deserializer)
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Bool => write!(f, "Bool"),
            Self::Bytes => write!(f, "Bytes"),
            Self::Int => write!(f, "Int"),
            Self::Ip => write!(f, "Ip"),
            Self::Array(ty) => write!(f, "Array<{}>", Type::from(*ty)),
            Self::Map(ty) => write!(f, "Map<{}>", Type::from(*ty)),
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
        *self
    }
}

impl GetType for CompoundType {
    fn get_type(&self) -> Type {
        (*self).into()
    }
}

impl PartialEq<&LhsValue<'_>> for LhsValue<'_> {
    fn eq(&self, other: &&LhsValue<'_>) -> bool {
        self.eq(*other)
    }
}

impl StrictPartialOrd<RhsValue> for LhsValue<'_> {}

impl PartialEq<RhsValue> for LhsValue<'_> {
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

mod private {
    use super::IntoValue;
    use crate::{TypedArray, TypedMap};
    use std::borrow::Cow;
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

    impl SealedIntoValue for &[u8] {}
    impl SealedIntoValue for Box<[u8]> {}
    impl SealedIntoValue for Vec<u8> {}
    impl SealedIntoValue for Cow<'_, [u8]> {}
    impl SealedIntoValue for &str {}
    impl SealedIntoValue for Box<str> {}
    impl SealedIntoValue for String {}
    impl SealedIntoValue for Cow<'_, str> {}

    impl SealedIntoValue for IpAddr {}
    impl SealedIntoValue for Ipv4Addr {}
    impl SealedIntoValue for Ipv6Addr {}

    impl<'a, V: IntoValue<'a>> SealedIntoValue for TypedArray<'a, V> {}
    impl<'a, V: IntoValue<'a>> SealedIntoValue for TypedMap<'a, V> {}
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

impl<'a> IntoValue<'a> for &'a [u8] {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Cow::Borrowed(self))
    }
}

impl<'a> IntoValue<'a> for Box<[u8]> {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Cow::Owned(Vec::from(self)))
    }
}

impl<'a> IntoValue<'a> for Vec<u8> {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Cow::Owned(self))
    }
}

impl<'a> IntoValue<'a> for Cow<'a, [u8]> {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(self)
    }
}

impl<'a> IntoValue<'a> for &'a str {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Cow::Borrowed(self.as_bytes()))
    }
}

impl<'a> IntoValue<'a> for Box<str> {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Cow::Owned(Vec::from(Box::<[u8]>::from(self))))
    }
}

impl<'a> IntoValue<'a> for String {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(Cow::Owned(self.into_bytes()))
    }
}

impl<'a> IntoValue<'a> for Cow<'a, str> {
    const TYPE: Type = Type::Bytes;

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Bytes(match self {
            Cow::Borrowed(slice) => Cow::Borrowed(slice.as_bytes()),
            Cow::Owned(vec) => Cow::Owned(vec.into()),
        })
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

impl From<RhsValue> for LhsValue<'_> {
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
            LhsValue::Array(array) => Some(Iter::IterArray(array.as_slice().iter())),
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
            Type::Bytes => Ok(LhsValue::Bytes(
                BytesOrString::deserialize(deserializer)?.into_bytes(),
            )),
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

pub(crate) enum Iter<'a> {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize, Hash, PartialOrd, Ord)]
enum PrimitiveType {
    Bool,
    Bytes,
    Int,
    Ip,
}

#[derive(Clone, Copy, Debug)]
enum Layer {
    Array,
    Map,
}

/// A type for field values that stores a recursive type in a flattened form. It
/// is particularly useful for creating nested types such as arrays or maps.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CompoundType {
    layers: u32,
    len: u8,
    primitive: PrimitiveType,
}

impl Serialize for CompoundType {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        Type::from(*self).serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CompoundType {
    #[inline]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Type::deserialize(deserializer).map(Self::from)
    }
}

impl CompoundType {
    #[inline]
    const fn new(ty: PrimitiveType) -> Self {
        Self {
            layers: 0,
            len: 0,
            primitive: ty,
        }
    }

    /// Converts a [`Type`] into a [`CompoundType`].
    #[inline]
    pub const fn from_type(ty: Type) -> Self {
        match match ty {
            Type::Bool => Some(Self::new(PrimitiveType::Bool)),
            Type::Bytes => Some(Self::new(PrimitiveType::Bytes)),
            Type::Int => Some(Self::new(PrimitiveType::Int)),
            Type::Ip => Some(Self::new(PrimitiveType::Ip)),
            Type::Array(ty) => ty.push(Layer::Array),
            Type::Map(ty) => ty.push(Layer::Map),
        } {
            Some(ty) => ty,
            None => panic!("Could not convert type to compound type"),
        }
    }

    /// Converts a [`CompoundType`] into a [`Type`].
    #[inline]
    pub const fn into_type(self) -> Type {
        let (ty, layer) = self.pop();
        match layer {
            Some(Layer::Array) => Type::Array(ty),
            Some(Layer::Map) => Type::Map(ty),
            None => match ty.primitive {
                PrimitiveType::Bool => Type::Bool,
                PrimitiveType::Bytes => Type::Bytes,
                PrimitiveType::Int => Type::Int,
                PrimitiveType::Ip => Type::Ip,
            },
        }
    }

    #[inline]
    const fn pop(mut self) -> (Self, Option<Layer>) {
        if self.len > 0 {
            // Maybe use (trailing/leading)_(ones/zeros) instead
            let is_array = (self.layers & 1) == 0;
            self.layers >>= 1;
            self.len -= 1;
            if is_array {
                (self, Some(Layer::Array))
            } else {
                (self, Some(Layer::Map))
            }
        } else {
            (self, None)
        }
    }

    #[inline]
    const fn push(mut self, layer: Layer) -> Option<Self> {
        if self.len >= 32 {
            None
        } else {
            let layer = match layer {
                Layer::Array => 0,
                Layer::Map => 1,
            };
            self.layers = (self.layers << 1) | layer;
            self.len += 1;
            Some(self)
        }
    }
}

impl From<PrimitiveType> for CompoundType {
    #[inline]
    fn from(ty: PrimitiveType) -> Self {
        Self::new(ty)
    }
}

impl From<Type> for CompoundType {
    #[inline]
    fn from(ty: Type) -> Self {
        Self::from_type(ty)
    }
}

impl From<CompoundType> for Type {
    #[inline]
    fn from(ty: CompoundType) -> Self {
        ty.into_type()
    }
}

declare_types!(
    /// A boolean.
    Bool(bool | UninhabitedBool | UninhabitedBool),

    /// A 64-bit integer number.
    Int(i64 | i64 | IntRange),

    /// An IPv4 or IPv6 address.
    ///
    /// These are represented as a single type to allow interop comparisons.
    Ip(IpAddr | IpAddr | IpRange),

    /// A raw bytes or a string field.
    ///
    /// These are completely interchangeable in runtime and differ only in
    /// syntax representation, so we represent them as a single type.
    Bytes(#[serde(borrow)] Cow<'a, [u8]> | Bytes | Bytes),

    /// An Array of [`Type`].
    Array[CompoundType](#[serde(skip_deserializing)] Array<'a> | UninhabitedArray | UninhabitedArray),

    /// A Map of string to [`Type`].
    Map[CompoundType](#[serde(skip_deserializing)] Map<'a> | UninhabitedMap | UninhabitedMap),
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

#[test]
fn test_type_serialize() {
    let ty = Type::Bool;
    assert_eq!(serde_json::to_string(&ty).unwrap(), "\"Bool\"");

    let ty = Type::Bytes;
    assert_eq!(serde_json::to_string(&ty).unwrap(), "\"Bytes\"");

    let ty = Type::Int;
    assert_eq!(serde_json::to_string(&ty).unwrap(), "\"Int\"");

    let ty = Type::Ip;
    assert_eq!(serde_json::to_string(&ty).unwrap(), "\"Ip\"");

    let ty = Type::Array(Type::Bytes.into());
    assert_eq!(serde_json::to_string(&ty).unwrap(), "{\"Array\":\"Bytes\"}");

    let ty = Type::Map(Type::Bytes.into());
    assert_eq!(serde_json::to_string(&ty).unwrap(), "{\"Map\":\"Bytes\"}");

    let ty = Type::Map(Type::Array(Type::Bytes.into()).into());
    assert_eq!(
        serde_json::to_string(&ty).unwrap(),
        "{\"Map\":{\"Array\":\"Bytes\"}}"
    );

    let ty = Type::Array(Type::Map(Type::Bytes.into()).into());
    assert_eq!(
        serde_json::to_string(&ty).unwrap(),
        "{\"Array\":{\"Map\":\"Bytes\"}}"
    );
}

#[test]
fn test_type_deserialize() {
    assert_eq!(
        serde_json::from_str::<'_, Type>("\"Bool\"").unwrap(),
        Type::Bool,
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("\"Bytes\"").unwrap(),
        Type::Bytes,
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("\"Int\"").unwrap(),
        Type::Int,
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("\"Ip\"").unwrap(),
        Type::Ip,
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("{\"Array\":\"Bytes\"}").unwrap(),
        Type::Array(Type::Bytes.into()),
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("{\"Map\":\"Bytes\"}").unwrap(),
        Type::Map(Type::Bytes.into()),
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("{\"Map\":{\"Array\":\"Bytes\"}}").unwrap(),
        Type::Map(Type::Array(Type::Bytes.into()).into()),
    );

    assert_eq!(
        serde_json::from_str::<'_, Type>("{\"Array\":{\"Map\":\"Bytes\"}}").unwrap(),
        Type::Array(Type::Map(Type::Bytes.into()).into()),
    );
}

#[test]
fn test_size_of_lhs_value() {
    assert_eq!(std::mem::size_of::<LhsValue<'_>>(), 48);
}
