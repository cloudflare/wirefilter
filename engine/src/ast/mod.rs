mod combined_expr;
mod field_expr;
mod function_expr;
mod simple_expr;

use self::combined_expr::CombinedExpr;
use crate::{
    filter::{CompiledExpr, Filter},
    lex::{LexResult, LexWith},
    scheme::{Field, Scheme, UnknownFieldError},
};
use serde::Serialize;
use std::fmt::{self, Debug};

trait Expr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + Serialize {
    fn uses(&self, field: Field<'s>) -> bool;
    fn compile(self) -> CompiledExpr<'s>;
}

/// A parsed filter AST.
///
/// It's attached to its corresponding [`Scheme`](struct@Scheme) because all
/// parsed fields are represented as indices and are valid only when
/// [`ExecutionContext`](::ExecutionContext) is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone)]
#[serde(transparent)]
pub struct FilterAst<'s> {
    #[serde(skip)]
    scheme: &'s Scheme,

    op: CombinedExpr<'s>,
}

impl<'s> Debug for FilterAst<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FilterAst<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (op, input) = CombinedExpr::lex_with(input, scheme)?;
        Ok((FilterAst { scheme, op }, input))
    }
}

impl<'s> FilterAst<'s> {
    /// Recursively checks whether a [`FilterAst`] uses a given field name.
    ///
    /// This is useful to lazily initialise expensive fields only if necessary.
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme
            .get_field_index(field_name)
            .map(|field| self.op.uses(field))
    }

    /// Compiles a [`FilterAst`] into a [`Filter`].
    pub fn compile(self) -> Filter<'s> {
        Filter::new(self.op.compile(), self.scheme)
    }
}
