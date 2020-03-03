use crate::{
    CompiledValueExpr, ExecutionContext, Field, FunctionCallArgExpr, FunctionCallExpr, IndexExpr,
    LhsValue, ListMatcherWrapper, Type, ValueExpr,
};

/// Trait used to represent a runtime context that will be used to execute a compiled [`Filter`].
pub trait ExecCtx {
    /// Fetches the value of a [`Field`].
    fn get_field_value_unchecked<'s>(&self, f: Field<'s>) -> &LhsValue<'_>;
    /// Fetches a [`ListMatcherWrapper`] given its [`Type`].
    fn get_list_matcher_unchecked(&self, t: &Type) -> &ListMatcherWrapper;
}

/// Trait used to drive the compilation of a [`FilterAst`] into a [`Filter`].
pub trait Compiler: Sized {
    /// ExecutionContext which will be used to execute a compiled [`Filter`].
    type ExecutionContext: ExecCtx;

    /// Compiles a [`ValueExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline(always)]
    fn compile_value_expr<'s>(&mut self, node: impl ValueExpr<'s>) -> CompiledValueExpr<'s, Self> {
        node.compile_with_compiler(self)
    }

    /// Compiles a [`FunctionCallExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline(always)]
    fn compile_function_call_expr<'s>(
        &mut self,
        node: FunctionCallExpr<'s>,
    ) -> CompiledValueExpr<'s, Self> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`FunctionCallArgExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline(always)]
    fn compile_function_call_arg_expr<'s>(
        &mut self,
        node: FunctionCallArgExpr<'s>,
    ) -> CompiledValueExpr<'s, Self> {
        self.compile_value_expr(node)
    }

    /// Compiles a [`IndexExpr`] node into a [`CompiledValueExpr`] (boxed closure).
    #[inline(always)]
    fn compile_index_expr<'s>(&mut self, node: IndexExpr<'s>) -> CompiledValueExpr<'s, Self> {
        self.compile_value_expr(node)
    }
}

/// Default compiler
#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultCompiler<'e> {
    _marker: std::marker::PhantomData<ExecutionContext<'e>>,
}

impl<'e> DefaultCompiler<'e> {
    /// Creates a new [`DefaultCompiler`].
    pub fn new() -> Self {
        Self::default()
    }
}

impl<'e> Compiler for DefaultCompiler<'e> {
    type ExecutionContext = ExecutionContext<'e>;
}
