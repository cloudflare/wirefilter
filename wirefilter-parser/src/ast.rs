#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub &'i str);

#[derive(Debug, PartialEq)]
pub enum Rhs {
    Int(i32),
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
