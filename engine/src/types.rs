use lex::{expect, skip_space, Lex, LexResult, LexWith};
use rhs_types::{Bytes, IpRange, UninhabitedBool};
use serde::{Deserialize, Serialize};
use std::{
    cmp::Ordering,
    fmt::{self, Debug, Formatter},
    net::IpAddr,
    ops::RangeInclusive,
};
use strict_partial_ord::StrictPartialOrd;

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
                    $($name::$variant(_) => Type::$variant,)*
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

    ($($(# $attrs:tt)* $name:ident ( $lhs_ty:ty | $rhs_ty:ty | $multi_rhs_ty:ty ) , )*) => {
        /// Enumeration of supported types for field values.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
        #[repr(u8)]
        pub enum Type {
            $($(# $attrs)* $name,)*
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

        declare_types! {
            /// An LHS value provided for filter execution.
            ///
            /// These are passed to the [execution context](::ExecutionContext)
            /// and are used by [compiled expressions](::CompiledExpr)
            /// for execution and comparisons.
            #[derive(PartialEq, Eq, Clone, Deserialize)]
            #[serde(untagged)]
            enum LhsValue<'a> {
                $($(# $attrs)* $name($lhs_ty),)*
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
                    $(Type::$name => {
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
                    $(Type::$name => {
                        let (value, input) = lex_rhs_values(input)?;
                        (RhsValues::$name(value), input)
                    })*
                })
            }
        }
    };
}

// special case for simply passing strings
impl<'a> From<&'a str> for LhsValue<'a> {
    fn from(s: &'a str) -> Self {
        s.as_bytes().into()
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
    Bytes(&'a [u8] | Bytes | Bytes),

    /// A 32-bit integer number.
    Int(i32 | i32 | RangeInclusive<i32>),

    /// A boolean.
    Bool(bool | UninhabitedBool | UninhabitedBool),
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
        LhsValue::Bytes(b"a JSON string with unicode \xE2\x9D\xA4")
    );

    /* Does not work because unicode escapes can't be borrowed directly from string
     * but require another temporary string in which they are decoded and that string
     * needs to be owned by someone, while LhsValue can hold only borrowed bytes
     */
    assert!(
        serde_json::from_str::<LhsValue<'_>>("\"a JSON string with escaped-unicode \\u2764\"")
            .is_err(),
        "LhsValue can only handle borrowed bytes"
    );

    let bytes: LhsValue<'_> = serde_json::from_str("\"1337\"").unwrap();
    assert_eq!(bytes, LhsValue::Bytes(b"1337"));

    let integer: LhsValue<'_> = serde_json::from_str("1337").unwrap();
    assert_eq!(integer, LhsValue::Int(1337));

    let b: LhsValue<'_> = serde_json::from_str("false").unwrap();
    assert_eq!(b, LhsValue::Bool(false));
}
