pub mod field_expr;
pub mod function_expr;
pub mod index_expr;
pub mod logical_expr;
pub mod parse;
pub mod visitor;

use self::index_expr::IndexExpr;
use self::logical_expr::LogicalExpr;
use self::parse::FilterParser;
use crate::{
    compiler::{Compiler, DefaultCompiler},
    filter::{CompiledExpr, CompiledValueExpr, Filter, FilterValue},
    lex::{LexErrorKind, LexResult, LexWith},
    scheme::{Scheme, UnknownFieldError},
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;
use std::fmt::{self, Debug};
use visitor::{UsesListVisitor, UsesVisitor, Visitor, VisitorMut};

/// Trait used to represent node that evaluates to a [`bool`] (or a [`Vec<bool>`]).
pub trait Expr:
    Sized + Eq + Debug + for<'i, 'p, 's> LexWith<'i, &'p FilterParser<'s>> + Serialize
{
    /// Recursively visit all nodes in the AST using a [`Visitor`].
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V);
    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V);
    /// Compiles current node into a [`CompiledExpr`] using [`Compiler`].
    fn compile_with_compiler<C: Compiler>(self, compiler: &mut C) -> CompiledExpr<C::U>;
    /// Compiles current node into a [`CompiledExpr`] using [`DefaultCompiler`].
    fn compile(self) -> CompiledExpr {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
}

/// Trait used to represent node that evaluates to an [`crate::LhsValue`].
pub trait ValueExpr:
    Sized + Eq + Debug + for<'i, 'p, 's> LexWith<'i, &'p FilterParser<'s>> + Serialize
{
    /// Recursively visit all nodes in the AST using a [`Visitor`].
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V);
    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V);
    /// Compiles current node into a [`CompiledValueExpr`] using [`Compiler`].
    fn compile_with_compiler<C: Compiler>(self, compiler: &mut C) -> CompiledValueExpr<C::U>;
    /// Compiles current node into a [`CompiledValueExpr`] using [`DefaultCompiler`].
    fn compile(self) -> CompiledValueExpr {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
}

/// A parsed filter AST.
///
/// It's attached to its corresponding [`Scheme`](struct@Scheme) because all
/// parsed fields are represented as indices and are valid only when
/// [`crate::ExecutionContext`] is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone, Hash)]
#[serde(transparent)]
pub struct FilterAst {
    #[serde(skip)]
    scheme: Scheme,

    op: LogicalExpr,
}

impl Debug for FilterAst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for FilterAst {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (op, input) = LogicalExpr::lex_with(input, parser)?;
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
            Type::Bool => Ok((
                FilterAst {
                    scheme: parser.scheme.clone(),
                    op,
                },
                input,
            )),
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

impl FilterAst {
    /// Returns the associated scheme.
    #[inline]
    pub fn scheme(&self) -> &Scheme {
        &self.scheme
    }

    /// Returns the associated expression.
    #[inline]
    pub fn expression(&self) -> &LogicalExpr {
        &self.op
    }

    /// Recursively visit all nodes in the AST using a [`Visitor`].
    #[inline]
    pub fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        visitor.visit_logical_expr(&self.op)
    }

    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    #[inline]
    pub fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        visitor.visit_logical_expr(&mut self.op)
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
    pub fn compile_with_compiler<C: Compiler>(self, compiler: &mut C) -> Filter<C::U> {
        match compiler.compile_logical_expr(self.op) {
            CompiledExpr::One(one) => Filter::new(one, self.scheme),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    /// Compiles a [`FilterAst`] into a [`Filter`] using the [`DefaultCompiler`].
    pub fn compile(self) -> Filter {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
}

/// A parsed value AST.
///
/// It's attached to its corresponding [`Scheme`](struct@Scheme) because all
/// parsed fields are represented as indices and are valid only when
/// [`crate::ExecutionContext`] is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone, Hash)]
#[serde(transparent)]
pub struct FilterValueAst {
    #[serde(skip)]
    scheme: Scheme,

    op: IndexExpr,
}

impl Debug for FilterValueAst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for FilterValueAst {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (op, rest) = IndexExpr::lex_with(input.trim(), parser)?;
        if op.map_each_count() > 0 {
            Err((
                LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: op.get_type().into(),
                    actual: Type::Array(op.get_type().into()),
                }),
                input,
            ))
        } else {
            Ok((
                FilterValueAst {
                    scheme: parser.scheme().clone(),
                    op,
                },
                rest,
            ))
        }
    }
}

impl FilterValueAst {
    /// Returns the associated scheme.
    #[inline]
    pub fn scheme(&self) -> &Scheme {
        &self.scheme
    }

    /// Returns the associated expression.
    #[inline]
    pub fn expression(&self) -> &IndexExpr {
        &self.op
    }

    /// Recursively visit all nodes in the AST using a [`Visitor`].
    #[inline]
    pub fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        visitor.visit_index_expr(&self.op)
    }

    /// Recursively visit all nodes in the AST using a [`VisitorMut`].
    #[inline]
    pub fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        visitor.visit_index_expr(&mut self.op)
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

    /// Compiles a [`FilterValueAst`] into a [`FilterValue`] using a specific [`Compiler`].
    pub fn compile_with_compiler<C: Compiler>(self, compiler: &mut C) -> FilterValue<C::U> {
        FilterValue::new(compiler.compile_index_expr(self.op), self.scheme)
    }

    /// Compiles a [`FilterValueAst`] into a [`FilterValue`] using the [`DefaultCompiler`].
    pub fn compile(self) -> FilterValue {
        let mut compiler = DefaultCompiler::new();
        self.compile_with_compiler(&mut compiler)
    }
}

impl GetType for FilterValueAst {
    #[inline]
    fn get_type(&self) -> Type {
        self.op.get_type()
    }
}
