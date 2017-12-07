extern crate wirefilter;

use std::env::args;
use std::marker::PhantomData;

use wirefilter::{CombiningOp, ComparisonOp, Context, Field, RhsValue, Type, UnaryOp};

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
    Combine(CombiningOp, Vec<Filter<'i>>),
    Unary(UnaryOp, Box<Filter<'i>>),
}

impl<'i> Context<'i> for AstContext<'i> {
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

    fn combine(self, mut lhs: Filter<'i>, op: CombiningOp, rhs: Filter<'i>) -> Filter<'i> {
        match lhs {
            Filter::Combine(lhs_op, ref mut filters) if op == lhs_op => {
                filters.push(rhs);
            }
            _ => {
                lhs = Filter::Combine(op, vec![lhs, rhs]);
            }
        }
        lhs
    }

    fn unary(self, op: UnaryOp, arg: Filter) -> Filter {
        Filter::Unary(op, Box::new(arg))
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
