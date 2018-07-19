mod combining;
mod field;
mod simple;

use self::combining::CombinedExpr;
use execution_context::ExecutionContext;
use lex::LexResult;
use scheme::{FieldIndex, Scheme};
use std::{
    fmt::{self, Debug},
    hash::{Hash, Hasher},
};

trait Expr<'s>: Sized {
    fn uses(&self, field: FieldIndex<'s>) -> bool;

    fn lex<'i>(scheme: &'s Scheme, input: &'i str) -> LexResult<'i, Self>;

    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool;
}

#[derive(PartialEq, Eq)]
pub struct Filter<'s> {
    scheme: &'s Scheme,
    op: CombinedExpr<'s>,
}

impl<'s> Hash for Filter<'s> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.op.hash(h)
    }
}

impl<'s> Debug for Filter<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl<'s> Filter<'s> {
    pub fn uses(&self, field_name: &str) -> bool {
        match self.scheme.get_field_index(field_name) {
            Some(field) => self.op.uses(field),
            None => false, // TODO: maybe we should panic on unknown field?
        }
    }

    pub fn lex<'i>(scheme: &'s Scheme, input: &'i str) -> LexResult<'i, Self> {
        let (op, input) = CombinedExpr::lex(scheme, input)?;
        Ok((Filter { scheme, op }, input))
    }

    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        if self.scheme != ctx.scheme() {
            panic!("Tried to execute filter parsed with a different scheme.");
        }

        self.op.execute(ctx)
    }
}
