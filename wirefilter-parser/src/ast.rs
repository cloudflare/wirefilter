use std::borrow::Cow;
use std::ops::RangeInclusive;

#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub Cow<'i, str>);

#[derive(Debug, PartialEq)]
pub struct Int(pub i32);

#[derive(Debug, PartialEq)]
pub struct Bytes<'i>(pub Cow<'i, [u8]>);

#[derive(Debug, PartialEq)]
pub struct IntRangeInclusive(pub RangeInclusive<i32>);

#[derive(Debug, PartialEq)]
pub enum Rhs<'i> {
    Int(Int),
    IntRangeInclusive(IntRangeInclusive),
    Bytes(Bytes<'i>),
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
