use {ErrorKind, Field, Lex, LexError, LexResult};
use bytes::Bytes;
use cidr::{Ipv4Cidr, Ipv6Cidr};
use op::{BytesOp, CombiningOp, ComparisonOp, OrderingMask, UnaryOp};
use op::UnsignedOp;
use regex::bytes::Regex;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::FromIterator;
use std::net::{Ipv4Addr, Ipv6Addr};
use utils::{expect, span};

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
            fn lex(input: &'a str, ty: Type) -> LexResult<Self> {
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

pub struct Context<K, T> {
    fields: HashMap<K, T>,
}

impl<K: Hash + Eq, T> FromIterator<(K, T)> for Context<K, T> {
    fn from_iter<I: IntoIterator<Item = (K, T)>>(iter: I) -> Self {
        Context {
            fields: HashMap::from_iter(iter),
        }
    }
}

fn combining_op(input: &str) -> (Option<CombiningOp>, &str) {
    match CombiningOp::lex(input) {
        Ok((op, input)) => (Some(op), input.trim_left()),
        Err(_) => (None, input),
    }
}

impl<K: Borrow<str> + Hash + Eq, T: GetType> Context<K, T> {
    fn simple_filter<'i>(&'i self, input: &'i str) -> LexResult<'i, Filter<'i>> {
        if let Ok(input) = expect(input, "(") {
            let input = input.trim_left();
            let (res, input) = self.combined_filter(input)?;
            let input = input.trim_left();
            let input = expect(input, ")")?;
            return Ok((res, input.trim_left()));
        }

        let initial_input = input;

        let (lhs, input) = Field::lex(input)?;

        let lhs_type = self.fields
            .get(lhs.path)
            .ok_or_else(|| (ErrorKind::UnknownField, lhs.path))?
            .get_type();

        let input = input.trim_left();

        let (op, input) = ComparisonOp::lex(input)?;

        let (filter, input) = match (lhs_type, op) {
            (_, ComparisonOp::Any(mask)) => {
                let (rhs, input) = RhsValue::lex(input, lhs_type)?;
                (Filter::Ordering(lhs, mask, rhs), input)
            }
            (Type::Unsigned, ComparisonOp::Unsigned(op)) => {
                let (rhs, input) = u64::lex(input)?;
                (Filter::Unsigned(lhs, op, rhs), input)
            }
            (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                BytesOp::Contains => {
                    let (rhs, input) = Bytes::lex(input)?;
                    (Filter::Contains(lhs, rhs), input)
                }
                BytesOp::Matches => {
                    let (rhs, input) = Regex::lex(input)?;
                    (Filter::Matches(lhs, rhs), input)
                }
            },
            (ty, op) => return Err((ErrorKind::UnsupportedOp(ty, op), span(initial_input, input))),
        };

        Ok((filter, input.trim_left()))
    }

    fn filter_prec<'i>(
        &'i self,
        mut lhs: Filter<'i>,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Filter<'i>> {
        while let Some(op) = lookahead.0 {
            let mut rhs = self.simple_filter(lookahead.1)?;
            loop {
                lookahead = combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = self.filter_prec(rhs.0, lookahead.0, lookahead)?;
            }
            match lhs {
                Filter::Combine(lhs_op, ref mut filters) if lhs_op == op => {
                    filters.push(rhs.0);
                }
                _ => {
                    lhs = Filter::Combine(op, vec![lhs, rhs.0]);
                }
            }
            if lookahead.0 < min_prec {
                // pretend we haven't seen an operator if its precedence is
                // outside of our limits
                lookahead = (None, rhs.1);
            }
        }
        Ok((lhs, lookahead.1))
    }

    fn combined_filter<'i>(&'i self, input: &'i str) -> LexResult<'i, Filter<'i>> {
        let (lhs, input) = self.simple_filter(input)?;
        let lookahead = combining_op(input);
        self.filter_prec(lhs, None, lookahead)
    }

    pub fn parse<'i>(&'i self, input: &'i str) -> Result<Filter<'i>, LexError<'i>> {
        let (res, input) = self.combined_filter(input)?;
        if input.is_empty() {
            Ok(res)
        } else {
            Err((ErrorKind::EOF, input))
        }
    }
}

#[derive(Debug)]
pub enum Filter<'i> {
    Ordering(Field<'i>, OrderingMask, RhsValue),
    Unsigned(Field<'i>, UnsignedOp, u64),
    Contains(Field<'i>, Bytes),
    Matches(Field<'i>, Regex),
    OneOf(Field<'i>, RhsValues),
    Combine(CombiningOp, Vec<Filter<'i>>),
    Unary(UnaryOp, Box<Filter<'i>>),
}
