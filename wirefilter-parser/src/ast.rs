#[derive(Debug, PartialEq)]
pub struct Var<'i>(pub &'i str);

#[derive(Debug, PartialEq)]
pub enum Rhs {
    Int(i32),
}
