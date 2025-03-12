use crate::{
    ComparisonExpr, CompiledExpr, CompiledValueExpr, Expr, FunctionCallArgExpr, FunctionCallExpr,
    IndexExpr, LogicalExpr, ValueExpr,
};

/// Trait used to drive the compilation of a [`crate::FilterAst`] into a [`crate::Filter`].
pub trait Compiler: Sized {
    /// The user data type passed in the  [`crate::ExecutionContext`].
    type U: 'static;

    /// Compiles a [`Expr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_expr(&mut self, node: impl Expr) -> CompiledExpr<Self::U> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`LogicalExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_logical_expr(&mut self, node: LogicalExpr) -> CompiledExpr<Self::U> {
        self.compile_expr(node)
    }

    /// Compiles a [`ComparisonExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_comparison_expr(&mut self, node: ComparisonExpr) -> CompiledExpr<Self::U> {
        self.compile_expr(node)
    }

    /// Compiles a [`ValueExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_value_expr(&mut self, node: impl ValueExpr) -> CompiledValueExpr<Self::U> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`FunctionCallExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_expr(&mut self, node: FunctionCallExpr) -> CompiledValueExpr<Self::U> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`FunctionCallArgExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_arg_expr(
        &mut self,
        node: FunctionCallArgExpr,
    ) -> CompiledValueExpr<Self::U> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`IndexExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_index_expr(&mut self, node: IndexExpr) -> CompiledValueExpr<Self::U> {
        self.compile_value_expr(node)
    }
}

/// Default compiler
#[derive(Clone, Copy, Debug)]
pub struct DefaultCompiler<U = ()> {
    _marker: std::marker::PhantomData<U>,
}

impl<U> Default for DefaultCompiler<U> {
    #[inline]
    fn default() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<U> DefaultCompiler<U> {
    /// Creates a new [`DefaultCompiler`].
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<U: 'static> Compiler for DefaultCompiler<U> {
    type U = U;
}
