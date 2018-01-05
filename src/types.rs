use {Lex, LexResult};
use bytes::Bytes;
use cidr::{Cidr, Ipv4Cidr, Ipv6Cidr};

use std::cmp::Ordering;
use std::net::{Ipv4Addr, Ipv6Addr};

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

        impl<$($name: ::std::fmt::Debug),*> ::std::fmt::Debug for Typed<$($name),*> {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                match *self {
                    $(Typed::$name(ref inner) => ::std::fmt::Debug::fmt(inner, f),)*
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

declare_types!(
    IpAddrV4(Ipv4Addr | Ipv4Cidr),
    IpAddrV6(Ipv6Addr | Ipv6Cidr),
    Bytes(Bytes),
    Unsigned(u64),
);

fn compare_ip<C: Cidr>(addr: &C::Address, network: &C) -> Ordering
where
    C::Address: Copy + PartialOrd,
{
    if addr > &network.last_address() {
        Ordering::Greater
    } else if addr < &network.first_address() {
        Ordering::Less
    } else {
        Ordering::Equal
    }
}

impl PartialOrd<RhsValue> for LhsValue {
    fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
        Some(match (self, other) {
            (&Typed::IpAddrV4(ref addr), &Typed::IpAddrV4(ref network)) => {
                compare_ip(addr, network)
            }
            (&Typed::IpAddrV6(ref addr), &Typed::IpAddrV6(ref network)) => {
                compare_ip(addr, network)
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
