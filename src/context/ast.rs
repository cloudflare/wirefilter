use std::marker::PhantomData;

use Field;
use context::{RhsValue, Type};
use op::{CombiningOp, ComparisonOp, UnaryOp};

#[derive(Clone, Copy)]
pub struct AstContext<'i>(PhantomData<&'i str>);

impl<'i> AstContext<'i> {
    pub fn new(_input: &'i str) -> Self {
        AstContext(PhantomData)
    }
}

#[derive(Debug)]
pub enum Filter<'i> {
    Compare(Field<'i>, ComparisonOp, RhsValue),
    OneOf(Field<'i>, Vec<RhsValue>),
    Combine(CombiningOp, Vec<Filter<'i>>),
    Unary(UnaryOp, Box<Filter<'i>>),
}

impl<'i> ::context::Context<'i> for AstContext<'i> {
    type LhsValue = Field<'i>;
    type Filter = Filter<'i>;

    fn get_field(self, path: &str) -> Option<Field> {
        Some(Field::new(path))
    }

    fn compare(self, lhs: Field, op: ComparisonOp, rhs: RhsValue) -> Result<Filter, Type> {
        if lhs.path == "err" {
            return Err(Type::Bytes);
        }
        Ok(Filter::Compare(lhs, op, rhs))
    }

    fn one_of<I: Iterator<Item = RhsValue>>(self, lhs: Field, rhs: I) -> Result<Filter, Type> {
        Ok(Filter::OneOf(lhs, rhs.collect()))
    }
}

impl<'i> ::context::Filter for Filter<'i> {
    fn combine(mut self, op: CombiningOp, other: Self) -> Self {
        match self {
            Filter::Combine(self_op, ref mut filters) if op == self_op => {
                filters.push(other);
            }
            _ => {
                self = Filter::Combine(op, vec![self, other]);
            }
        }
        self
    }

    fn unary(self, op: UnaryOp) -> Self {
        Filter::Unary(op, Box::new(self))
    }
}
