use lex::{expect, skip_space, Lex, LexResult, LexWith};
use rhs_types::{Bytes, UninhabitedBool};
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
    ($(# $attrs:tt)* enum $name:ident $(<$lt:tt>)* { $($variant:ident ( $ty:ty ) , )* }) => {
        $(# $attrs)*
        #[repr(u8)]
        pub enum $name $(<$lt>)* {
            $($variant($ty),)*
        }

        impl $(<$lt>)* GetType for $name $(<$lt>)* {
            fn get_type(&self) -> Type {
                match self {
                    $($name::$variant(_) => Type::$variant,)*
                }
            }
        }

        impl $(<$lt>)* Debug for $name $(<$lt>)* {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    $($name::$variant(inner) => Debug::fmt(inner, f),)*
                }
            }
        }
    };

    ($($name:ident ( $lhs_ty:ty | $rhs_ty:ty | $multi_rhs_ty:ty ) , )*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
        #[repr(u8)]
        pub enum Type {
            $($name,)*
        }

        pub trait GetType {
            fn get_type(&self) -> Type;
        }

        impl GetType for Type {
            fn get_type(&self) -> Type {
                *self
            }
        }

        declare_types! {
            #[derive(Clone)]
            enum LhsValue<'a> {
                $($name($lhs_ty),)*
            }
        }

        $(impl<'a> From<$lhs_ty> for LhsValue<'a> {
            fn from(value: $lhs_ty) -> Self {
                LhsValue::$name(value)
            }
        })*

        declare_types! {
            #[derive(PartialEq, Eq, Clone, Serialize)]
            #[serde(untagged)]
            enum RhsValue {
                $($name($rhs_ty),)*
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValue {
            fn lex_with(input: &str, ty: Type) -> LexResult<Self> {
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
            #[derive(PartialEq, Eq, Clone, Serialize)]
            #[serde(untagged)]
            enum RhsValues {
                $($name(Vec<$multi_rhs_ty>),)*
            }
        }

        impl<'i> LexWith<'i, Type> for RhsValues {
            fn lex_with(input: &str, ty: Type) -> LexResult<Self> {
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
    Ip(IpAddr | IpAddr | RangeInclusive<IpAddr>),
    Bytes(&'a [u8] | Bytes | Bytes),
    Int(i32 | i32 | RangeInclusive<i32>),
    Bool(bool | UninhabitedBool | UninhabitedBool),
);
