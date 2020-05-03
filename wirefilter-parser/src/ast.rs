use std::borrow::Cow;
use std::ops::RangeInclusive;

#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub Cow<'i, str>);

#[derive(Debug, PartialEq)]
pub enum Rhs<'i> {
    Int(i32),
    IntRangeInclusive(RangeInclusive<i32>),
    Bytes(Cow<'i, [u8]>),
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
