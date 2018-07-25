use lex::{expect, Lex, LexResult, LexWith};
use rhs_types::{Bytes, IpCidr};
use std::{
    cmp::Ordering,
    fmt::{self, Debug, Formatter},
    net::IpAddr,
    ops::Deref,
};

fn lex_rhs_values<'i, T: Lex<'i>>(input: &'i str) -> LexResult<Vec<T>> {
    let mut input = expect(input, "{")?.trim_left();
    let mut res = Vec::new();
    loop {
        let (item, rest) = T::lex(input)?;
        res.push(item);
        input = rest.trim_left();
        if let Ok(input) = expect(input, "}") {
            return Ok((res, input));
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

        declare_types!(@enum #[derive(PartialEq, Eq, Hash, Clone)] RhsValue {
            $($name($rhs_ty),)*
        });

        declare_types!(@enum #[derive(PartialEq, Eq, Hash, Clone)] RhsValues {
            $($name(Vec<$rhs_ty>),)*
        });

        impl<'a> PartialOrd<RhsValue> for LhsValue<'a> {
            fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
                match (self, other) {
                    $((LhsValue::$name(lhs), RhsValue::$name(rhs)) => {
                        lhs.deref().partial_cmp(rhs.deref())
                    },)*
                    _ => None,
                }
            }
        }

        impl<'a> PartialEq<RhsValue> for LhsValue<'a> {
            fn eq(&self, other: &RhsValue) -> bool {
                self.partial_cmp(other) == Some(Ordering::Equal)
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

        impl RhsValues {
            pub fn contains(&self, lhs: &LhsValue) -> bool {
                match (self, lhs) {
                    $((RhsValues::$name(values), LhsValue::$name(lhs)) => {
                        values.iter().any(|rhs| lhs.deref() == rhs.deref())
                    })*
                    _ => false,
                }
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
    Bytes(&'a [u8] | Bytes),
    Unsigned(u64 | u64),
    Bool(bool | bool),
);
