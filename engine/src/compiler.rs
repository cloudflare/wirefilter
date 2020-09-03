use crate::{
    ComparisonExpr, CompiledExpr, CompiledValueExpr, Expr, FunctionCallArgExpr, FunctionCallExpr,
    IndexExpr, LogicalExpr, SimpleExpr, ValueExpr,
};

/// Trait used to drive the compilation of a [`FilterAst`] into a [`Filter`].
pub trait Compiler<'s, U: 's = ()>: Sized + 's {
    /// Compiles a [`Expr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_expr(&mut self, node: impl Expr<'s>) -> CompiledExpr<'s, U> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`SimpleExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_simple_expr(&mut self, node: SimpleExpr<'s>) -> CompiledExpr<'s, U> {
        self.compile_expr(node)
    }

    /// Compiles a [`LogicalExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_logical_expr(&mut self, node: LogicalExpr<'s>) -> CompiledExpr<'s, U> {
        self.compile_expr(node)
    }

    /// Compiles a [`ComparisonExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_comparison_expr(&mut self, node: ComparisonExpr<'s>) -> CompiledExpr<'s, U> {
        self.compile_expr(node)
    }

    /// Compiles a [`ValueExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_value_expr(&mut self, node: impl ValueExpr<'s>) -> CompiledValueExpr<'s, U> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`FunctionCallExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_expr(
        &mut self,
        node: FunctionCallExpr<'s>,
    ) -> CompiledValueExpr<'s, U> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`FunctionCallArgExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_arg_expr(
        &mut self,
        node: FunctionCallArgExpr<'s>,
    ) -> CompiledValueExpr<'s, U> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`IndexExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_index_expr(&mut self, node: IndexExpr<'s>) -> CompiledValueExpr<'s, U> {
        self.compile_value_expr(node)
    }
}

/// Default compiler
#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultCompiler {}

impl DefaultCompiler {
    /// Creates a new [`DefaultCompiler`].
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'s, U: 's> Compiler<'s, U> for DefaultCompiler {}
