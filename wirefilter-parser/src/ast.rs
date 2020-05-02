use std::ops::RangeInclusive;

#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub &'i str);

#[derive(Debug, PartialEq)]
pub struct Int(pub i32);

#[derive(Debug, PartialEq)]
pub struct IntRangeInclusive(pub RangeInclusive<i32>);

#[derive(Debug, PartialEq)]
pub enum Rhs {
    Int(Int),
    IntRangeInclusive(IntRangeInclusive),
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
pub struct Expr<'i> {
    pub var: Var<'i>,
    pub op: BinOp,
    pub rhs: Rhs,
}
