use bytes::Bytes;
use ip_addr::IpCidr;
use lex::{Lex, LexResult};
use lex::expect;

use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::net::IpAddr;

fn lex_rhs_values<'a, T: Lex<'a>>(input: &'a str) -> LexResult<Vec<T>> {
    let mut input = expect(input, "{")?.trim_left();
    let mut res = Vec::new();
    loop {
        let (item, rest) = T::lex(input)?;
        res.push(item);
        input = rest.trim_left();
        if let Ok(input) = expect(input, "}") {
            return Ok((res, input.trim_left()));
        }
    }
}

macro_rules! declare_types {
    (@enum $name:ident { $($variant:ident ( $ty:ty ) , )* }) => {
        #[derive(Serialize, Deserialize)]
        pub enum $name {
            $($variant($ty),)*
        }

        impl GetType for $name {
            fn get_type(&self) -> Type {
                match *self {
                    $($name::$variant(_) => Type::$variant,)*
                }
            }
        }

        impl Debug for $name {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match *self {
                    $($name::$variant(ref inner) => Debug::fmt(inner, f),)*
                }
            }
        }
    };

    ($($name:ident ( $lhs_ty:ty | $rhs_ty:ty ) , )*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

        declare_types!(@enum LhsValue {
            $($name($lhs_ty),)*
        });

        declare_types!(@enum RhsValue {
            $($name($rhs_ty),)*
        });

        declare_types!(@enum RhsValues {
            $($name(Vec<$rhs_ty>),)*
        });

        impl PartialOrd<RhsValue> for LhsValue {
            fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
                match (self, other) {
                    $((&LhsValue::$name(ref lhs), &RhsValue::$name(ref rhs)) => {
                        lhs.partial_cmp(rhs)
                    },)*
                    _ => None,
                }
            }
        }

        impl PartialEq<RhsValue> for LhsValue {
            fn eq(&self, other: &RhsValue) -> bool {
                match (self, other) {
                    $((&LhsValue::$name(ref lhs), &RhsValue::$name(ref rhs)) => lhs == rhs,)*
                    _ => false,
                }
            }
        }

        impl RhsValue {
            pub fn lex(input: &str, ty: Type) -> LexResult<Self> {
                Ok(match ty {
                    $(Type::$name => {
                        let (value, input) = <$rhs_ty>::lex(input)?;
                        (RhsValue::$name(value), input)
                    })*
                })
            }
        }

        impl RhsValues {
            pub fn lex(input: &str, ty: Type) -> LexResult<Self> {
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

declare_types!(
    Ip(IpAddr | IpCidr),
    Bytes(Bytes | Bytes),
    Unsigned(u64 | u64),
);
