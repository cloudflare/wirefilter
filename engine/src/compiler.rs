use crate::{
    ComparisonExpr, CompiledExpr, CompiledValueExpr, ContextFamily, Expr, Field, FieldBindingError,
    FieldConsumer, FunctionCallArgExpr, FunctionCallExpr, IndexExpr, LogicalExpr,
    StoredContextFamily, ValueExpr,
};

/// Trait used to drive the compilation of a [`crate::FilterAst`] into a [`crate::Filter`].
pub trait Compiler: Sized {
    /// The user data type passed in the  [`crate::ExecutionContext`].
    type U: 'static;

    /// Context and concrete field bindings used by compiled expressions.
    type Family: ContextFamily<UserData = Self::U>;

    /// Resolve a field while retaining the concrete getter type during compilation.
    /// The binding takes ownership so the compiled expression can retain the field
    /// without cloning it.
    #[inline]
    fn bind_field<B: FieldConsumer<Self::Family>>(
        &mut self,
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError> {
        Self::Family::bind(field, consumer)
    }

    /// Compiles a [`Expr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_expr(&mut self, node: impl Expr) -> CompiledExpr<Self::U, Self::Family> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`LogicalExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_logical_expr(&mut self, node: LogicalExpr) -> CompiledExpr<Self::U, Self::Family> {
        self.compile_expr(node)
    }

    /// Compiles a [`ComparisonExpr`] node into a [`CompiledExpr`] (boxed closure).
    #[inline]
    fn compile_comparison_expr(
        &mut self,
        node: ComparisonExpr,
    ) -> CompiledExpr<Self::U, Self::Family> {
        self.compile_expr(node)
    }

    /// Compiles a [`ValueExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_value_expr(
        &mut self,
        node: impl ValueExpr,
    ) -> CompiledValueExpr<Self::U, Self::Family> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`FunctionCallExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_expr(
        &mut self,
        node: FunctionCallExpr,
    ) -> CompiledValueExpr<Self::U, Self::Family> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`FunctionCallArgExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_function_call_arg_expr(
        &mut self,
        node: FunctionCallArgExpr,
    ) -> CompiledValueExpr<Self::U, Self::Family> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`IndexExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline]
    fn compile_index_expr(&mut self, node: IndexExpr) -> CompiledValueExpr<Self::U, Self::Family> {
        self.compile_value_expr(node)
    }
}

/// Default compiler
pub struct DefaultCompiler<U = (), F = StoredContextFamily<U>> {
    _marker: std::marker::PhantomData<fn() -> (U, F)>,
}

impl<U, F> Copy for DefaultCompiler<U, F> {}

impl<U, F> Clone for DefaultCompiler<U, F> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<U, F> std::fmt::Debug for DefaultCompiler<U, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DefaultCompiler").finish()
    }
}

impl<U, F> Default for DefaultCompiler<U, F> {
    #[inline]
    fn default() -> Self {
        Self {
            _marker: std::marker::PhantomData,
        }
    }
}

impl<U, F> DefaultCompiler<U, F> {
    /// Creates a new [`DefaultCompiler`].
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<U: 'static, F: ContextFamily<UserData = U>> Compiler for DefaultCompiler<U, F> {
    type Family = F;
    type U = U;
}
