use bytes::Bytes;
use ip_addr::IpCidr;
use lex::{Lex, LexResult};
use lex::expect;
use op::OrderingOp;

use std::borrow::Cow;
use std::fmt::{self, Debug, Formatter};
use std::net::IpAddr;
use std::ops::Deref;

fn lex_rhs_values<'i, T: Lex<'i>>(input: &'i str) -> LexResult<Vec<T>> {
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
    (@enum $(# $attrs:tt)* $name:ident $(<$lt:tt>)* { $($variant:ident ( $ty:ty ) , )* }) => {
        $(# $attrs)*
        pub enum $name $(<$lt>)* {
            $($variant($ty),)*
        }

        impl $(<$lt>)* GetType for $name $(<$lt>)* {
            fn get_type(&self) -> Type {
                match *self {
                    $($name::$variant(_) => Type::$variant,)*
                }
            }
        }

        impl $(<$lt>)* Debug for $name $(<$lt>)* {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match *self {
                    $($name::$variant(ref inner) => Debug::fmt(inner, f),)*
                }
            }
        }
    };

    ($($name:ident ( $lhs_ty:ty | $rhs_ty:ty ) , )*) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

        declare_types!(@enum #[repr(u8)] #[derive(Clone)] LhsValue<'a> {
            $($name($lhs_ty),)*
        });

        declare_types!(@enum #[derive(PartialEq, Eq, Hash)] RhsValue {
            $($name($rhs_ty),)*
        });

        declare_types!(@enum #[derive(PartialEq, Eq, Hash)] RhsValues {
            $($name(Vec<$rhs_ty>),)*
        });

        impl<'a> LhsValue<'a> {
            pub fn try_cmp(&self, op: OrderingOp, other: &RhsValue) -> Result<bool, ()> {
                let opt_ordering = match (self, other) {
                    $((&LhsValue::$name(ref lhs), &RhsValue::$name(ref rhs)) => {
                        lhs.deref().partial_cmp(rhs.deref())
                    },)*
                    _ => return Err(()),
                };
                Ok(op.matches_opt(opt_ordering))
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

            pub fn try_contains(&self, lhs: &LhsValue) -> Result<bool, ()> {
                Ok(match (self, lhs) {
                    $((&RhsValues::$name(ref values), &LhsValue::$name(ref lhs)) => {
                        values.iter().any(|rhs| lhs.deref() == rhs.deref())
                    })*
                    _ => return Err(()),
                })
            }
        }
    };
}

impl<'i> Lex<'i> for bool {
    fn lex(_input: &str) -> LexResult<Self> {
        // Boolean fields should be checked without parsing RHS value
        unreachable!()
    }
}

declare_types!(
    Ip(IpAddr | IpCidr),
    Bytes(Cow<'a, [u8]> | Bytes),
    Unsigned(u64 | u64),
    Bool(bool | bool),
);
