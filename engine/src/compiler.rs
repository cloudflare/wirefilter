use crate::{
    ComparisonExpr, CompiledExpr, CompiledValueExpr, Expr, FunctionCallArgExpr, FunctionCallExpr,
    IndexExpr, LogicalExpr, ValueExpr,
};

/// Trait used to drive the compilation of a [`FilterAst`] into a [`Filter`].
pub trait Compiler<'s>: Sized + 's {
    /// The user data type passed in the  [`ExecutionContext`].
    type U;

    /// Compiles a [`Expr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_expr(&mut self, node: impl Expr<'s>) -> CompiledExpr<'s, Self::U> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`LogicalExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_logical_expr(&mut self, node: LogicalExpr<'s>) -> CompiledExpr<'s, Self::U> {
        self.compile_expr(node)
    }

    /// Compiles a [`ComparisonExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_comparison_expr(&mut self, node: ComparisonExpr<'s>) -> CompiledExpr<'s, Self::U> {
        self.compile_expr(node)
    }

    /// Compiles a [`ValueExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_value_expr(&mut self, node: impl ValueExpr<'s>) -> CompiledValueExpr<'s, Self::U> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`FunctionCallExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_expr(
        &mut self,
        node: FunctionCallExpr<'s>,
    ) -> CompiledValueExpr<'s, Self::U> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`FunctionCallArgExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_arg_expr(
        &mut self,
        node: FunctionCallArgExpr<'s>,
    ) -> CompiledValueExpr<'s, Self::U> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`IndexExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_index_expr(&mut self, node: IndexExpr<'s>) -> CompiledValueExpr<'s, Self::U> {
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

impl<'s, U: 's> Compiler<'s> for DefaultCompiler<U> {
    type U = U;
}
