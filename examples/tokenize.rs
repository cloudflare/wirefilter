extern crate wirefilter;

use std::env::args;
use std::marker::PhantomData;

use wirefilter::op::{CombiningOp, ComparisonOp, UnaryOp};
use wirefilter::Field;
use wirefilter::context::{RhsValue, Type};

#[derive(Clone, Copy)]
struct AstContext<'i>(PhantomData<&'i str>);

impl<'i> AstContext<'i> {
    pub fn new(_input: &'i str) -> Self {
        AstContext(PhantomData)
    }
}

#[derive(Debug)]
enum Filter<'i> {
    Compare(Field<'i>, ComparisonOp, RhsValue),
    OneOf(Field<'i>, Vec<RhsValue>),
    Combine(CombiningOp, Vec<Filter<'i>>),
    Unary(UnaryOp, Box<Filter<'i>>),
}

impl<'i> wirefilter::context::Context<'i> for AstContext<'i> {
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

impl<'i> wirefilter::context::Filter for Filter<'i> {
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

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let context = AstContext::new(&filter);

    match wirefilter::filter(&filter, context) {
        Ok(res) => println!("{:#?}", res),
        Err((err, input)) => panic!("{} in {:?}", err, input),
    }
}
