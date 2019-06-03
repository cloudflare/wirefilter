mod combined_expr;
mod field_expr;
mod function_expr;
mod index_expr;
mod simple_expr;

use self::combined_expr::CombinedExpr;
use crate::{
    filter::{CompiledValueExpr, Filter},
    lex::{LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme, UnknownFieldError},
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;
use std::fmt::{self, Debug};

trait Expr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + Serialize {
    fn uses(&self, field: Field<'s>) -> bool;
    fn compile(self) -> CompiledValueExpr<'s>;
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
        // CombinedExpr::lex_with can return an AST where the root is an
        // CombinedExpr::Combining of [`Type::Array(Box::New(Type::Bool))`].
        //
        // It must do this because we need to be able to use
        // CombinedExpr::Combining of [`Type::Array(Box::New(Type::Bool))`]
        // as arguments to functions, however it should not be valid as a
        // filter expression itself.
        //
        // Here we enforce the constraint that the root of the AST, a
        // CombinedExpr, must evaluate to [`Type::Bool`].
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
            .get_field_index(field_name)
            .map(|field| self.op.uses(field))
    }

    /// Compiles a [`FilterAst`] into a [`Filter`].
    pub fn compile(self) -> Filter<'s> {
        Filter::new(self.op.compile(), self.scheme)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lazy_static::lazy_static;

    lazy_static! {
        static ref SCHEME: Scheme = {
            let scheme: Scheme = Scheme! {
                foo: Array(Bool),
                bar: Bool,
            };
            scheme
        };
    }

    #[test]
    fn test_filter_ast_lex_with_bad_expr() {
        // assert that Array(Bool) is not a valid expr
        assert_err!(
            FilterAst::lex_with(r#"foo"#, &SCHEME),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            r#""#
        );

        // assert that Array(Bool) and Array(Bool) is not a valid expr
        assert_err!(
            FilterAst::lex_with(r#"foo and foo"#, &SCHEME),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            r#""#
        );

        // assert that Array(Bool) and (Array(Bool) and Bool) is not a valid expr
        assert_err!(
            FilterAst::lex_with(r#"foo and (foo and bar)"#, &SCHEME),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            r#")"#
        );

        // assert that Array(Bool) and Bool is not a valid expr
        assert_err!(
            FilterAst::lex_with(r#"foo and bar"#, &SCHEME),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            r#""#
        );
    }
}
