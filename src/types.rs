use lex::expect;
use bytes::Bytes;
use cidr::{Cidr, IpCidr};
use lex::{Lex, LexResult};

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
                        let (values, input) = lex_rhs_values(input)?;
                        (RhsValues::$name(values), input)
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

impl PartialOrd<RhsValue> for LhsValue {
    fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
        Some(match (self, other) {
            (&LhsValue::Ip(ref addr), &RhsValue::Ip(ref network)) => {
                if addr > &network.last_address() {
                    Ordering::Greater
                } else if addr < &network.first_address() {
                    Ordering::Less
                } else {
                    Ordering::Equal
                }
            }
            (&LhsValue::Bytes(ref lhs), &RhsValue::Bytes(ref rhs)) => lhs.cmp(rhs),
            (&LhsValue::Unsigned(ref lhs), &RhsValue::Unsigned(ref rhs)) => lhs.cmp(rhs),
            _ => return None,
        })
    }
}

impl PartialEq<RhsValue> for LhsValue {
    fn eq(&self, other: &RhsValue) -> bool {
        match self.partial_cmp(other) {
            Some(Ordering::Equal) => true,
            _ => false,
        }
    }
}
