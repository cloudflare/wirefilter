//! Each AST expression node gets compiled into a CompiledExpr or a CompiledValueExpr.
//! Therefore, Filter essentialy is a public API facade for a tree of Compiled(Value)Exprs.
//! When filter gets executed it calls `execute` method on its root expression which then
//! under the hood propagates field values to its leafs by recursively calling
//! their `execute` methods and aggregating results into a single boolean value
//! as recursion unwinds.

use crate::{
    compiler::Compiler,
    scheme::{Scheme, SchemeMismatchError},
    types::{LhsValue, Type},
};

/// Boxed closure for [`Expr`] AST node that evaluates to a simple [`bool`].
#[allow(clippy::type_complexity)]
pub struct CompiledOneExpr<'s, C: Compiler + 's>(
    Box<dyn for<'e> Fn(&'e C::ExecutionContext) -> bool + Sync + Send + 's>,
);

impl<'s, C: Compiler + 's> CompiledOneExpr<'s, C> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e C::ExecutionContext) -> bool + Sync + Send + 's,
    ) -> Self {
        CompiledOneExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e C::ExecutionContext) -> bool {
        self.0(ctx)
    }
}

pub(crate) type CompiledVecExprResult = Box<[bool]>;

/// Boxed closure for [`Expr`] AST node that evaluates to a list of [`bool`].
#[allow(clippy::type_complexity)]
pub struct CompiledVecExpr<'s, C: Compiler + 's>(
    Box<dyn for<'e> Fn(&'e C::ExecutionContext) -> CompiledVecExprResult + Sync + Send + 's>,
);

impl<'s, C: Compiler + 's> CompiledVecExpr<'s, C> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e C::ExecutionContext) -> CompiledVecExprResult + Sync + Send + 's,
    ) -> Self {
        CompiledVecExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e C::ExecutionContext) -> CompiledVecExprResult {
        self.0(ctx)
    }
}

/// Enum of boxed closure for [`Expr`] AST nodes.
pub enum CompiledExpr<'s, C: Compiler> {
    /// Variant for [`Expr`] AST node that evaluates to a simple [`bool`].
    One(CompiledOneExpr<'s, C>),
    /// Variant for [`Expr`] AST node that evaluates to a list of [`bool`].
    Vec(CompiledVecExpr<'s, C>),
}

impl<'s, C: Compiler + 's> CompiledExpr<'s, C> {
    #[cfg(test)]
    pub(crate) fn execute_one<'e>(&self, ctx: &'e C::ExecutionContext) -> bool {
        match self {
            CompiledExpr::One(one) => one.execute(ctx),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    #[cfg(test)]
    pub(crate) fn execute_vec<'e>(&self, ctx: &'e C::ExecutionContext) -> CompiledVecExprResult {
        match self {
            CompiledExpr::One(_) => unreachable!(),
            CompiledExpr::Vec(vec) => vec.execute(ctx),
        }
    }
}

pub type CompiledValueResult<'a> = Result<LhsValue<'a>, Type>;

impl<'a> From<LhsValue<'a>> for CompiledValueResult<'a> {
    fn from(value: LhsValue<'a>) -> Self {
        Ok(value)
    }
}

impl<'a> From<Type> for CompiledValueResult<'a> {
    fn from(ty: Type) -> Self {
        Err(ty)
    }
}

/// Boxed closure for [`ValueExpr`] AST node that evaluates to an [`LhsValue`].
#[allow(clippy::type_complexity)]
pub struct CompiledValueExpr<'s, C: Compiler + 's>(
    Box<dyn for<'e> Fn(&'e C::ExecutionContext) -> CompiledValueResult<'e> + Sync + Send + 's>,
);

impl<'s, C: Compiler + 's> CompiledValueExpr<'s, C> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e C::ExecutionContext) -> CompiledValueResult<'e> + Sync + Send + 's,
    ) -> Self {
        CompiledValueExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e C::ExecutionContext) -> CompiledValueResult<'e>
    where
        C::ExecutionContext: 'e,
    {
        self.0(ctx)
    }
}

/// An IR for a compiled filter expression.
///
/// Currently it works by creating and combining boxed untyped closures and
/// performing indirect calls between them, which is fairly cheap, but,
/// surely, not as fast as an inline code with real JIT compilers.
///
/// On the other hand, it's much less risky than allocating, trusting and
/// executing code at runtime, because all the code being executed is
/// already statically generated and verified by the Rust compiler and only the
/// data differs. For the same reason, our "compilation" times are much better
/// than with a full JIT compiler as well.
///
/// In the future the underlying representation might change, but for now it
/// provides the best trade-off between safety and performance of compilation
/// and execution.
pub struct Filter<'s, C: Compiler> {
    root_expr: CompiledOneExpr<'s, C>,
    scheme: &'s Scheme,
}

impl<'s, C: Compiler + 's> Filter<'s, C> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledOneExpr<'s, C>, scheme: &'s Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a filter against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e C::ExecutionContext) -> Result<bool, SchemeMismatchError>
    where
        C::ExecutionContext: PartialEq<Scheme>,
    {
        if ctx == self.scheme {
            Ok(self.root_expr.execute(ctx))
        } else {
            Err(SchemeMismatchError)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Filter, SchemeMismatchError};
    use crate::execution_context::ExecutionContext;

    #[test]
    fn test_scheme_mismatch() {
        let scheme1 = Scheme! { foo: Int };
        let scheme2 = Scheme! { foo: Int, bar: Int };
        let filter = scheme1.parse("foo == 42").unwrap().compile();
        let ctx = ExecutionContext::new(&scheme2);

        assert_eq!(filter.execute(&ctx), Err(SchemeMismatchError));
    }

    #[test]
    fn ensure_send_and_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        is_send::<Filter>();
        is_sync::<Filter>();
    }
}
