use crate::{
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    rhs_types::{Bytes, IpRange, UninhabitedArray, UninhabitedBool, UninhabitedMap},
    scheme::{FieldIndex, IndexAccessError},
    strict_partial_ord::StrictPartialOrd,
};
use failure::Fail;
use serde::{Deserialize, Serialize};
use std::{
    borrow::Cow,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    convert::TryFrom,
    fmt::{self, Debug, Formatter},
    iter::once,
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
#[derive(Debug, PartialEq, Fail)]
#[fail(
    display = "expected value of type {:?}, but got {:?}",
    expected, actual
)]
pub struct TypeMismatchError {
    /// Expected value type.
    pub expected: ExpectedTypeList,
    /// Provided value type.
    pub actual: Type,
}

/// An error that occurs on a type mismatch.
#[derive(Debug, PartialEq, Fail)]
pub enum SetValueError {
    #[fail(display = "{}", _0)]
    TypeMismatch(#[cause] TypeMismatchError),
    #[fail(display = "{}", _0)]
    IndexAccess(#[cause] IndexAccessError),
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
        #[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize, Hash)]
        pub enum Type {
            $($(# $attrs)* $name$(($val_ty))?,)*
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

/// An array of [`Type`].
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Array<'a> {
    val_type: Type,
    #[serde(borrow)]
    data: Vec<LhsValue<'a>>,
}

impl<'a> Array<'a> {
    /// Creates a new array
    pub fn new(val_type: Type) -> Self {
        Self {
            val_type,
            data: Vec::new(),
        }
    }

    /// Get a reference to an element if it exists
    pub fn get(&self, idx: usize) -> Option<&LhsValue<'a>> {
        self.data.get(idx)
    }

    /// Get a mutable reference to an element if it exists
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut LhsValue<'a>> {
        self.data.get_mut(idx)
    }

    /// Inserts an element at index `idx`
    pub fn insert(&mut self, idx: usize, value: LhsValue<'a>) -> Result<(), TypeMismatchError> {
        let value_type = value.get_type();
        if self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone().into(),
                actual: value_type,
            });
        }
        self.data.insert(idx, value);
        Ok(())
    }

    /// Push an element to the back of the array
    pub fn push(&mut self, value: LhsValue<'a>) -> Result<(), TypeMismatchError> {
        let value_type = value.get_type();
        if self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone().into(),
                actual: value_type,
            });
        }
        self.data.push(value);
        Ok(())
    }

    pub(crate) fn to_owned<'b>(&self) -> Array<'b> {
        let mut arr = Array {
            val_type: self.val_type.clone(),
            data: Default::default(),
        };
        for v in self.data.iter() {
            arr.data.push(v.to_owned());
        }
        arr
    }

    pub(crate) fn as_ref(&'a self) -> Array<'a> {
        let mut arr = Array {
            val_type: self.val_type.clone(),
            data: Default::default(),
        };
        for v in self.data.iter() {
            arr.data.push(v.as_ref());
        }
        arr
    }

    /// Returns the type of the contained values.
    pub fn value_type(&self) -> &Type {
        &self.val_type
    }
}

impl<'a> GetType for Array<'a> {
    fn get_type(&self) -> Type {
        Type::Array(Box::new(self.val_type.clone()))
    }
}

impl<'a> IntoIterator for Array<'a> {
    type Item = LhsValue<'a>;
    type IntoIter = std::vec::IntoIter<LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

impl<'a> IntoIterator for &'a Array<'a> {
    type Item = &'a LhsValue<'a>;
    type IntoIter = std::slice::Iter<'a, LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.data).iter()
    }
}

impl<'a> Extend<LhsValue<'a>> for Array<'a> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = LhsValue<'a>>,
    {
        let value_type = self.value_type().clone();
        self.data.extend(
            iter.into_iter()
                .inspect(|elem| assert!(elem.get_type() == value_type)),
        )
    }
}

/// A map of string to [`Type`].
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Map<'a> {
    val_type: Type,
    #[serde(borrow)]
    data: HashMap<Box<[u8]>, LhsValue<'a>>,
}

impl<'a> Map<'a> {
    /// Creates a new map
    pub fn new(val_type: Type) -> Self {
        Self {
            val_type,
            data: HashMap::new(),
        }
    }

    /// Get a reference to an element if it exists
    pub fn get(&self, key: &[u8]) -> Option<&LhsValue<'a>> {
        self.data.get(key)
    }

    /// Inserts an element, returns the previously inserted
    /// element if it exists.
    pub fn insert(&mut self, key: &[u8], value: LhsValue<'a>) -> Result<(), TypeMismatchError> {
        let value_type = value.get_type();
        if self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone().into(),
                actual: value_type,
            });
        }
        self.data.insert(
            {
                let mut vec = Vec::with_capacity(key.len());
                vec.extend(key);
                vec.into_boxed_slice()
            },
            value,
        );
        Ok(())
    }

    pub(crate) fn to_owned<'b>(&self) -> Map<'b> {
        let mut map = Map {
            val_type: self.val_type.clone(),
            data: Default::default(),
        };
        for (k, v) in self.data.iter() {
            map.data.insert(k.clone(), v.to_owned());
        }
        map
    }

    pub(crate) fn as_ref(&'a self) -> Map<'a> {
        let mut map = Map {
            val_type: self.val_type.clone(),
            data: Default::default(),
        };
        for (k, v) in self.data.iter() {
            map.data.insert(k.clone(), v.as_ref());
        }
        map
    }

    /// Returns the type of the contained values.
    pub fn value_type(&self) -> &Type {
        &self.val_type
    }
}

impl<'a> GetType for Map<'a> {
    fn get_type(&self) -> Type {
        Type::Map(Box::new(self.val_type.clone()))
    }
}

impl<'a> IntoIterator for Map<'a> {
    type Item = (Box<[u8]>, LhsValue<'a>);
    type IntoIter = std::collections::hash_map::IntoIter<Box<[u8]>, LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
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
            RhsValue::Array(a) => match *a {},
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
            LhsValue::Array(a) => LhsValue::Array(a.as_ref()),
            LhsValue::Map(m) => LhsValue::Map(m.as_ref()),
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
            (LhsValue::Map(map), FieldIndex::MapKey(ref key)) => Ok(map.data.get(key.as_bytes())),
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
            LhsValue::Array(a) => LhsValue::Array(a.to_owned()),
            LhsValue::Map(m) => LhsValue::Map(m.to_owned()),
        }
    }

    /// Returns an iterator over the Map or Array
    pub fn iter(&'a self) -> Option<Iter<'a>> {
        match self {
            LhsValue::Array(array) => Some(Iter::IterArray((&array.data).iter())),
            LhsValue::Map(map) => Some(Iter::IterMap((&map.data).iter())),
            _ => None,
        }
    }
}

pub enum IntoIter<'a> {
    IntoArray(std::vec::IntoIter<LhsValue<'a>>),
    IntoMap(std::collections::hash_map::IntoIter<Box<[u8]>, LhsValue<'a>>),
}

impl<'a> Iterator for IntoIter<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        match self {
            IntoIter::IntoArray(array) => array.next(),
            IntoIter::IntoMap(map) => map.next().map(|(_, v)| v),
        }
    }
}

impl<'a> IntoIterator for LhsValue<'a> {
    type Item = LhsValue<'a>;
    type IntoIter = IntoIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        match self {
            LhsValue::Array(array) => IntoIter::IntoArray(array.into_iter()),
            LhsValue::Map(map) => IntoIter::IntoMap(map.into_iter()),
            _ => unreachable!(),
        }
    }
}

pub enum Iter<'a> {
    IterArray(std::slice::Iter<'a, LhsValue<'a>>),
    IterMap(std::collections::hash_map::Iter<'a, Box<[u8]>, LhsValue<'a>>),
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
    Array[Box<Type>](Array<'a> | UninhabitedArray | UninhabitedArray),

    /// A Map of string to [`Type`].
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
