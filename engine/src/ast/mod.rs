mod combined_expr;
mod field_expr;
mod simple_expr;

use self::combined_expr::CombinedExpr;
use compiled_expr::CompiledExpr;
use lex::{LexResult, LexWith};
use scheme::{Field, Scheme, UnknownFieldError};
use serde::Serialize;
use std::fmt::{self, Debug};

trait Expr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + Serialize {
    fn uses(&self, field: Field<'s>) -> bool;
    fn compile(self) -> CompiledExpr<'s>;
}

/// A parsed filter AST.
///
/// It's attached to its corresponding [`Scheme`] because all parsed fields
/// are represented as indices and are valid only when [`ExecutionContext`]
/// is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone)]
#[serde(transparent)]
pub struct Filter<'s> {
    #[serde(skip)]
    scheme: &'s Scheme,

    op: CombinedExpr<'s>,
}

impl<'s> Debug for Filter<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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
    /// Recursively checks whether a [`Filter`] uses a given field name.
    ///
    /// This is useful to lazily initialise expensive fields only if necessary.
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme
            .get_field_index(field_name)
            .map(|field| self.op.uses(field))
    }

    /// Compiles a [`Filter`] into a compiled expression IR.
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
