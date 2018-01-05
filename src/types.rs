use bytes::Bytes;
use cidr::{Cidr, IpCidr};
use lex::{Lex, LexResult};

use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::net::IpAddr;

macro_rules! declare_types {
    (@declare_rhs { $($prev:ty,)* } $name:ident ( $lhs_ty:ty | $rhs_ty:ty ), $($rest:tt)*) => {
        declare_types!(@declare_rhs { $($prev,)* $rhs_ty, } $($rest)*);
    };

    (@declare_rhs { $($prev:ty,)* } $name:ident ( $ty:ty ), $($rest:tt)*) => {
        declare_types!(@declare_rhs { $($prev,)* $ty, } $($rest)*);
    };

    (@declare_rhs { $($ty:ty,)* }) => {
        pub type RhsValue = Typed<$($ty),*>;

        pub type RhsValues = Typed<$(Vec<$ty>),*>;
    };

    ($($name:ident ( $lhs_ty:ty $(| $rhs_ty:ty)* ),)*) => {
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

        pub enum Typed<$($name),*> {
            $($name($name),)*
        }

        impl<$($name),*> GetType for Typed<$($name),*> {
            fn get_type(&self) -> Type {
                match *self {
                    $(Typed::$name(_) => Type::$name,)*
                }
            }
        }

        impl<$($name: Debug),*> Debug for Typed<$($name),*> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match *self {
                    $(Typed::$name(ref inner) => Debug::fmt(inner, f),)*
                }
            }
        }

        impl<'a $(, $name: Lex<'a>)*> Typed<$($name),*> {
            pub fn lex(input: &'a str, ty: Type) -> LexResult<Self> {
                Ok(match ty {
                    $(Type::$name => {
                        let (value, input) = $name::lex(input)?;
                        (Typed::$name(value), input)
                    })*
                })
            }
        }

        pub type LhsValue = Typed<$($lhs_ty),*>;

        declare_types!(@declare_rhs {} $($name ( $lhs_ty $(| $rhs_ty)* ),)*);
    };
}

declare_types!(Ip(IpAddr | IpCidr), Bytes(Bytes), Unsigned(u64),);

impl PartialOrd<RhsValue> for LhsValue {
    fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
        Some(match (self, other) {
            (&Typed::Ip(ref addr), &Typed::Ip(ref network)) => {
                if addr > &network.last_address() {
                    Ordering::Greater
                } else if addr < &network.first_address() {
                    Ordering::Less
                } else {
                    Ordering::Equal
                }
            }
            (&Typed::Bytes(ref lhs), &Typed::Bytes(ref rhs)) => lhs.cmp(rhs),
            (&Typed::Unsigned(ref lhs), &Typed::Unsigned(ref rhs)) => lhs.cmp(rhs),
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
