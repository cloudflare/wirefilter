use crate::lex::{Lex, LexResult, LexWith, expect, skip_space};
use crate::lhs_types::{LhsValue, LhsValueSeed};
use crate::rhs_types::{
    BytesExpr, IntRange, IpRange, UninhabitedArray, UninhabitedBool, UninhabitedMap,
};
use serde::de::{DeserializeSeed, Deserializer};
use serde::{Deserialize, Serialize, Serializer};
use std::collections::BTreeSet;
use std::convert::TryFrom;
use std::fmt::{self, Debug, Formatter};
use std::iter::once;
use std::net::IpAddr;
use thiserror::Error;

fn lex_literal_set<'i, T: Lex<'i>>(input: &'i str) -> LexResult<'i, Vec<T>> {
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
    ($name:ident($val_ty:ty)) => {
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

// This macro generates `Type`, `LiteralValue`, and `LiteralSet`.
// `lhs_types` generates `LhsValue` from the same `with_value_types` table.
//
// Before the parenthesis is the variant for the `Type` enum (`Type::Ip`).
// First argument is the corresponding `LhsValue` variant (`LhsValue::Ip(IpAddr)`).
// Second argument is the corresponding `LiteralValue` variant (`LiteralValue::Ip(IpAddr)`).
// Third argument is the corresponding `LiteralSet` variant (`LiteralSet::Ip(Vec<IpRange>)`) for the curly bracket syntax. eg `num in {1, 5}`
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
    ($($(# $attrs:tt)* $name:ident $([$val_ty:ty])? ( $(# $lhs_attrs:tt)* $lhs_ty:ty | $literal_ty:ty | $literal_set_ty:ty ) , )*) => {
        /// Enumeration of supported types for field values.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize, Serialize, Hash, PartialOrd, Ord)]
        pub enum Type {
            $($(# $attrs)* $name$(($val_ty))?,)*
        }

        declare_types! {
            /// A literal value parsed from a filter string.
            #[derive(PartialEq, Eq, Clone, Hash, Serialize)]
            #[serde(untagged)]
            enum LiteralValue {
                $($(# $attrs)* $name($literal_ty),)*
            }
        }

        impl<'i> LexWith<'i, Type> for LiteralValue {
            fn lex_with(input: &str, ty: Type) -> LexResult<'_, Self> {
                Ok(match ty {
                    $(replace_underscore!($name $(($val_ty))?) => {
                        let (value, input) = <$literal_ty>::lex(input)?;
                        (LiteralValue::$name(value), input)
                    })*
                })
            }
        }

        $(impl<'a> TryFrom<LiteralValue> for $literal_ty {
            type Error = TypeMismatchError;

            fn try_from(value: LiteralValue) -> Result<$literal_ty, TypeMismatchError> {
                match value {
                    LiteralValue::$name(value) => Ok(value),
                    _ => Err(TypeMismatchError {
                        expected: specialized_try_from!($name).into(),
                        actual: value.get_type(),
                    }),
                }
            }
        })*

        $(impl<'a> TryFrom<&'a LiteralValue> for &'a $literal_ty {
            type Error = TypeMismatchError;

            fn try_from(value: &'a LiteralValue) -> Result<&'a $literal_ty, TypeMismatchError> {
                match value {
                    LiteralValue::$name(value) => Ok(value),
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
            enum LiteralSet {
                $($(# $attrs)* $name(Vec<$literal_set_ty>),)*
            }
        }

        impl From<LiteralValue> for LiteralSet {
            fn from(literal: LiteralValue) -> Self {
                match literal {
                    $(LiteralValue::$name(literal) => {
                        #[allow(unreachable_code)]
                        LiteralSet::$name(vec![literal.into()])
                    })*
                }
            }
        }

        impl LiteralSet {
            /// Appends a value to the back of the collection.
            pub fn push(&mut self, literal: LiteralValue) -> Result<(), TypeMismatchError> {
                match self {
                    $(LiteralSet::$name(vec) => match literal {
                        LiteralValue::$name(literal) => {
                            #[allow(unreachable_code)]
                            Ok(vec.push(literal.into()))
                        }
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: literal.get_type(),
                        }),
                    },)*
                }
            }

            /// Moves all the values of `other` into `self`, leaving `other` empty.
            pub fn append(&mut self, other: &mut Self) -> Result<(), TypeMismatchError> {
                match self {
                    $(LiteralSet::$name(vec) => match other {
                        LiteralSet::$name(other) => Ok(vec.append(other)),
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
                    $(LiteralSet::$name(vec) => match other {
                        LiteralSet::$name(other) => Ok(vec.extend(other)),
                        _ => Err(TypeMismatchError {
                            expected: self.get_type().into(),
                            actual: other.get_type(),
                        }),
                    },)*
                }
            }
        }

        impl<'i> LexWith<'i, Type> for LiteralSet {
            fn lex_with(input: &str, ty: Type) -> LexResult<'_, Self> {
                Ok(match ty {
                    $(replace_underscore!($name $(($val_ty))?) => {
                        let (value, input) = lex_literal_set(input)?;
                        (LiteralSet::$name(value), input)
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

// Keep the variants and their storage/literal representations in one place.
// Each definition module expands its own types and implementations.
macro_rules! with_value_types {
    ($declare:ident) => {
        $declare! {
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
            Bytes(#[serde(borrow)] Bytes<'a> | BytesExpr | BytesExpr),

            /// An Array of [`Type`].
            Array[CompoundType](#[serde(skip_deserializing)] Array<'a> | UninhabitedArray | UninhabitedArray),

            /// A Map of string to [`Type`].
            Map[CompoundType](#[serde(skip_deserializing)] Map<'a> | UninhabitedMap | UninhabitedMap),
        }
    };
}

pub(crate) use declare_types;
pub(crate) use specialized_get_type;
pub(crate) use specialized_try_from;
pub(crate) use with_value_types;

with_value_types!(declare_types);

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
