use super::{CombiningOp, ComparisonOp, RhsValue, Type, UnaryOp};

pub trait Context<'i>: Copy {
    type LhsValue;
    type Filter;

    fn get_field(self, path: &'i str) -> Option<Self::LhsValue>;
    fn compare(
        self,
        lhs: Self::LhsValue,
        op: ComparisonOp,
        rhs: RhsValue,
    ) -> Result<Self::Filter, Type>;
    fn combine(self, lhs: Self::Filter, op: CombiningOp, rhs: Self::Filter) -> Self::Filter;
    fn unary(self, op: UnaryOp, arg: Self::Filter) -> Self::Filter;
}

pub mod execution;
