use crate::{
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    rhs_types::{Bytes, IpRange, UninhabitedBool, UninhabitedMap},
    scheme::{FieldIndex, IndexAccessError},
    strict_partial_ord::StrictPartialOrd,
};
use failure::Fail;
use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::HashMap,
    fmt::{self, Debug, Formatter},
    net::IpAddr,
    ops::RangeInclusive,
};

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

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Fail)]
#[fail(
    display = "expected value of type {:?}, but got {:?}",
    expected, actual
)]
pub struct TypeMismatchError {
    /// Expected value type.
    pub expected: Type,
    /// Provided value type.
    pub actual: Type,
}

macro_rules! replace_underscore {
    ($name:ident ($val_ty:ty)) => {Type::$name(_)};
    ($name:ident) => {Type::$name};
}

macro_rules! specialized_get_type {
    (Map, $value:ident) => {
        Type::Map(Box::new($value.get_type()))
    };
    ($name:ident, $value:ident) => {
        Type::$name
    };
}

macro_rules! declare_types {
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

    ($($(# $attrs:tt)* $name:ident $([$val_ty:ty])? ( $(# $lhs_attrs:tt)* $lhs_ty:ty | $rhs_ty:ty | $multi_rhs_ty:ty ) , )*) => {
        /// Enumeration of supported types for field values.
        #[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
        #[repr(C)]
        pub enum Type {
            $($(# $attrs)* $name$(($val_ty))?,)*
        }

        impl Type {
            /// Returns the inner type when available (e.g: for a Map)
            pub fn next(&self) -> Option<Type> {
                match self {
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

        declare_types! {
            /// An RHS value parsed from a filter string.
            #[derive(PartialEq, Eq, Clone, Serialize)]
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

        impl<'a> StrictPartialOrd<RhsValue> for LhsValue<'a> {}

        impl<'a> PartialEq<RhsValue> for LhsValue<'a> {
            fn eq(&self, other: &RhsValue) -> bool {
                self.strict_partial_cmp(other) == Some(Ordering::Equal)
            }
        }

        declare_types! {
            /// A typed group of a list of values.
            ///
            /// This is used for `field in { ... }` operation that allows
            /// only same-typed values in a list.
            #[derive(PartialEq, Eq, Clone, Serialize)]
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

/// A map of string to [`Type`].
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Map<'a> {
    val_type: Type,
    #[serde(borrow)]
    data: HashMap<String, LhsValue<'a>>,
}

impl<'a> Map<'a> {
    pub fn new(val_type: Type) -> Self {
        Self {
            val_type,
            data: HashMap::new(),
        }
    }

    pub fn get(&self, key: &str) -> Option<&LhsValue<'a>> {
        self.data.get(key)
    }

    pub fn insert(
        &mut self,
        key: String,
        value: LhsValue<'a>,
    ) -> Result<Option<LhsValue<'a>>, TypeMismatchError> {
        let value_type = value.get_type();
        if self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone(),
                actual: value_type,
            });
        }
        Ok(self.data.insert(key, value))
    }

    pub fn to_owned<'b>(&self) -> Map<'b> {
        let mut map = Map {
            val_type: self.val_type.clone(),
            data: Default::default(),
        };
        for (k, v) in self.data.iter() {
            map.data.insert(k.clone(), v.to_owned());
        }
        map
    }
}

impl<'a> GetType for Map<'a> {
    fn get_type(&self) -> Type {
        self.val_type.clone()
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

impl<'a> From<&'a RhsValue> for LhsValue<'a> {
    fn from(rhs_value: &'a RhsValue) -> Self {
        match rhs_value {
            RhsValue::Ip(ip) => LhsValue::Ip(*ip),
            RhsValue::Bytes(bytes) => LhsValue::Bytes(Cow::Borrowed(bytes)),
            RhsValue::Int(integer) => LhsValue::Int(*integer),
            RhsValue::Bool(b) => match *b {},
            RhsValue::Map(m) => match *m {},
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
            LhsValue::Map(m) => LhsValue::Map(m.clone()),
        }
    }

    /// Retrieve an element from an LhsValue given a path item and a specified
    /// type.
    /// Returns a TypeMismatchError error if current type does not support it
    /// nested element. Only LhsValue::Map supports nested elements for now.
    pub fn get(&'a self, item: &FieldIndex) -> Result<Option<&'a LhsValue<'a>>, IndexAccessError> {
        match (self, item) {
            (LhsValue::Map(map), FieldIndex::MapKey(ref name)) => Ok(map.data.get(name)),
            (_, FieldIndex::MapKey(_name)) => Err(IndexAccessError {
                index: item.clone(),
                actual: self.get_type(),
            }),
        }
    }

    /// Deep clone of an LhsValue.
    /// Will convert any Cow::Borrowed to Cow::Owned and copy
    /// already existing Cow::Owned.
    pub fn to_owned<'b>(&self) -> LhsValue<'b> {
        match &self {
            LhsValue::Ip(ip) => LhsValue::Ip(*ip),
            LhsValue::Bytes(bytes) => match bytes {
                Cow::Borrowed(raw) => LhsValue::Bytes(Cow::Owned(raw.to_vec())),
                Cow::Owned(raw) => LhsValue::Bytes(Cow::Owned(raw.to_vec())),
            },
            LhsValue::Int(integer) => LhsValue::Int(*integer),
            LhsValue::Bool(b) => LhsValue::Bool(*b),
            LhsValue::Map(m) => LhsValue::Map(m.to_owned()),
        }
    }
}

declare_types!(
    /// An IPv4 or IPv6 field.
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

    /// A map of string to [`Type`].
    Map[Box<Type>](Map<'a> | UninhabitedMap | UninhabitedMap),
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
