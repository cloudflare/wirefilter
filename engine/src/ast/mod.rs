mod combined_expr;
mod field_expr;
mod simple_expr;

use self::combined_expr::CombinedExpr;
use execution_context::ExecutionContext;
use lex::{LexResult, LexWith};
use scheme::{Field, Scheme, UnknownFieldError};
use std::fmt::{self, Debug};

pub struct CompiledExpr<'s>(Box<dyn 's + Fn(&ExecutionContext<'s>) -> bool>);

impl<'s> CompiledExpr<'s> {
    pub fn new(closure: impl 's + Fn(&ExecutionContext<'s>) -> bool) -> Self {
        CompiledExpr(Box::new(closure))
    }

    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        self.0(ctx)
    }
}

trait Expr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + ::serde::Serialize {
    fn uses(&self, field: Field<'s>) -> bool;
    fn compile(self) -> CompiledExpr<'s>;
}

#[derive(PartialEq, Eq, Serialize, Clone)]
#[serde(transparent)]
pub struct Filter<'s> {
    #[serde(skip)]
    scheme: &'s Scheme,

    op: CombinedExpr<'s>,
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

    pub fn compile(self) -> CompiledExpr<'s> {
        let scheme = self.scheme;
        let op = self.op.compile();

        CompiledExpr::new(move |ctx| {
            if scheme != ctx.scheme() {
                panic!("Tried to execute filter parsed with a different scheme.");
            }

            op.execute(ctx)
        })
    }
}
