pub mod field_expr;
pub mod function_expr;
pub mod index_expr;
pub mod logical_expr;
pub mod simple_expr;
pub mod visitor;

use self::logical_expr::LogicalExpr;
use crate::{
    compiler::{Compiler, DefaultCompiler},
    filter::{CompiledExpr, CompiledValueExpr, Filter},
    lex::{LexErrorKind, LexResult, LexWith},
    scheme::{Scheme, UnknownFieldError},
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;
use std::fmt::{self, Debug};
use visitor::{UsesListVisitor, UsesVisitor, Visitor, VisitorMut};

/// Trait used to represent node that evaluates to a [`bool`] (or a [`Vec<bool>`]).
pub trait Expr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + Serialize {
    /// Recursively visit all nodes in the AST.
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V);
    /// Recursively visit all nodes in the AST.
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V);
    /// Compiles current node into a [`CompiledExpr`] using [`Compiler`].
    fn compile_with_compiler<C: Compiler + 's>(self, compiler: &mut C) -> CompiledExpr<'s, C>;
    /// Compiles current node into a [`CompiledExpr`] using [`DefaultCompiler`].
    fn compile(self) -> CompiledExpr<'s, DefaultCompiler<'s>> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
}

/// Trait used to represent node that evaluates to an [`LhsValue`].
pub trait ValueExpr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + Serialize {
    /// Recursively visit all nodes in the AST.
    fn walk<V: Visitor<'s>>(&self, visitor: &mut V);
    /// Recursively visit all nodes in the AST.
    fn walk_mut<V: VisitorMut<'s>>(&mut self, visitor: &mut V);
    /// Compiles current node into a [`CompiledValueExpr`] using [`Compiler`].
    fn compile_with_compiler<C: Compiler + 's>(self, compiler: &mut C) -> CompiledValueExpr<'s, C>;
    /// Compiles current node into a [`CompiledValueExpr`] using [`DefaultCompiler`].
    fn compile(self) -> CompiledValueExpr<'s, DefaultCompiler<'s>> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
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
    /// Recursively visit all nodes in the AST.
    pub fn walk<V: Visitor<'s>>(&self, visitor: &mut V) {
        visitor.visit_logical_expr(&self.op)
    }

    /// Recursively checks whether a [`FilterAst`] uses a given field name.
    ///
    /// This is useful to lazily initialise expensive fields only if necessary.
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme.get_field(field_name).map(|field| {
            let mut visitor = UsesVisitor::new(field);
            self.walk(&mut visitor);
            visitor.uses()
        })
    }

    /// Recursively checks whether a [`FilterAst`] uses a list.
    pub fn uses_list(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme.get_field(field_name).map(|field| {
            let mut visitor = UsesListVisitor::new(field);
            self.walk(&mut visitor);
            visitor.uses()
        })
    }

    /// Compiles a [`FilterAst`] into a [`Filter`] using a specific [`Compiler`].
    pub fn compile_with_compiler<C: Compiler + 's>(self, compiler: &mut C) -> Filter<'s, C> {
        match self.op.compile_with_compiler(compiler) {
            CompiledExpr::One(one) => Filter::new(one, self.scheme),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    /// Compiles a [`FilterAst`] into a [`Filter`] using [`DefaultCompiler`].
    pub fn compile(self) -> Filter<'s, DefaultCompiler<'s>> {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
}
