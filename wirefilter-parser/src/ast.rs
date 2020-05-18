use cidr::{Ipv4Cidr, Ipv6Cidr};
use regex::bytes::RegexBuilder;
use std::borrow::Cow;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::ops::{Deref, RangeInclusive};
use std::str::FromStr;

#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub Cow<'i, str>);

#[derive(Debug)]
pub struct Regex(regex::bytes::Regex);

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
    Regex(Regex),
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

impl PartialEq for Regex {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0.as_str() == other.0.as_str()
    }
}

impl Deref for Regex {
    type Target = regex::bytes::Regex;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FromStr for Regex {
    type Err = regex::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        RegexBuilder::new(s).unicode(false).build().map(Regex)
    }
}
