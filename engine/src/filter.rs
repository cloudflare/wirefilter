use field::Field;
use op::{CombiningOp, OrderingOp, UnaryOp, UnsignedOp};
use re::Regex;
use types::{RhsValue, RhsValues};

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum FilterOp {
    Ordering(OrderingOp, RhsValue),
    Unsigned(UnsignedOp, u64),
    Matches(Regex),
    OneOf(RhsValues),
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Filter<'a> {
    Op(Field<'a>, FilterOp),
    Combine(CombiningOp, Vec<Filter<'a>>),
    Unary(UnaryOp, Box<Filter<'a>>),
}

impl<'a> Filter<'a> {
    pub fn uses(&self, field: Field) -> bool {
        match *self {
            Filter::Op(lhs, ..) => field == lhs,
            Filter::Combine(_, ref filters) => filters.iter().any(|filter| filter.uses(field)),
            Filter::Unary(_, ref filter) => filter.uses(field),
        }
    }
}
