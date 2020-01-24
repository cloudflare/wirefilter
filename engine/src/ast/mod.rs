mod field_expr;
mod function_expr;
mod index_expr;
mod logical_expr;
mod simple_expr;

use self::logical_expr::LogicalExpr;
use crate::{
    filter::{CompiledExpr, Filter},
    lex::{LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme, UnknownFieldError},
    types::{GetType, Type, TypeMismatchError},
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

    op: LogicalExpr<'s>,
}

impl<'s> Debug for FilterAst<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FilterAst<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (op, input) = LogicalExpr::lex_with(input, scheme)?;
        // LogicalExpr::lex_with can return an AST where the root is an
        // LogicalExpr::Combining of type [`Array(Bool)`].
        //
        // It must do this because we need to be able to use
        // LogicalExpr::Combining of type [`Array(Bool)`]
        // as arguments to functions, however it should not be valid as a
        // filter expression itself.
        //
        // Here we enforce the constraint that the root of the AST, a
        // LogicalExpr, must evaluate to type [`Bool`].
        let ty = op.get_type();
        match ty {
            Type::Bool => Ok((FilterAst { scheme, op }, input)),
            _ => Err((
                LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: Type::Bool.into(),
                    actual: ty,
                }),
                input,
            )),
        }
    }
}

impl<'s> FilterAst<'s> {
    /// Recursively checks whether a [`FilterAst`] uses a given field name.
    ///
    /// This is useful to lazily initialise expensive fields only if necessary.
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme
            .get_field(field_name)
            .map(|field| self.op.uses(field))
    }

    /// Compiles a [`FilterAst`] into a [`Filter`].
    pub fn compile(self) -> Filter<'s> {
        match self.op.compile() {
            CompiledExpr::One(one) => Filter::new(one, self.scheme),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }
}
