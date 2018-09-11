mod combined_expr;
mod field_expr;
mod simple_expr;

use self::combined_expr::CombinedExpr;
use execution_context::ExecutionContext;
use lex::{LexResult, LexWith};
use scheme::{Field, Scheme, UnknownFieldError};
use std::{
    fmt::{self, Debug},
    hash::{Hash, Hasher},
};

trait Expr<'s>: Sized + Eq + Hash + Debug + for<'i> LexWith<'i, &'s Scheme> {
    fn uses(&self, field: Field<'s>) -> bool;
    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool;
}

#[derive(PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct Filter<'s> {
    #[serde(skip)]
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

impl<'i, 's> LexWith<'i, &'s Scheme> for Filter<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (op, input) = CombinedExpr::lex_with(input, scheme)?;
        Ok((Filter { scheme, op }, input))
    }
}

impl<'s> Filter<'s> {
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme
            .get_field_index(field_name)
            .map(|field| self.op.uses(field))
    }

    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        if self.scheme != ctx.scheme() {
            panic!("Tried to execute filter parsed with a different scheme.");
        }

        self.op.execute(ctx)
    }
}
