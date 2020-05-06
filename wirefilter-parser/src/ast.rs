use cidr::{Ipv4Cidr, Ipv6Cidr};
use std::borrow::Cow;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::ops::RangeInclusive;

#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub Cow<'i, str>);

#[derive(Debug, PartialEq)]
pub enum Rhs<'i> {
    Int(i32),
    IntRange(RangeInclusive<i32>),
    String(Cow<'i, [u8]>),
    Ipv4(Ipv4Addr),
    Ipv6(Ipv6Addr),
    Ipv4Range(RangeInclusive<Ipv4Addr>),
    Ipv6Range(RangeInclusive<Ipv6Addr>),
    Ipv4Cidr(Ipv4Cidr),
    Ipv6Cidr(Ipv6Cidr),
}

#[derive(Debug, PartialEq)]
pub enum BinOp {
    Eq,
    NotEq,
    GreaterOrEq,
    LessOrEq,
    Greater,
    Less,
    BitwiseAnd,
    Contains,
    Matches,
    In,
}

#[derive(Debug, PartialEq)]
pub enum Expr<'i> {
    Unary(Var<'i>),
    Binary {
        lhs: Var<'i>,
        op: BinOp,
        rhs: Rhs<'i>,
    },
}
