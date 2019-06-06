use crate::{
    execution_context::ExecutionContext,
    scheme::Scheme,
    types::{LhsValue, Type},
};
use failure::Fail;

/// An error that occurs if filter and provided [`ExecutionContext`] have
/// different [schemes](struct@Scheme).
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "execution context doesn't match the scheme with which filter was parsed")]
pub struct SchemeMismatchError;

// Each AST expression node gets compiled into CompiledExpr. Therefore, Filter
// essentialy is a public API facade for a tree of CompiledExprs. When filter
// gets executed it calls `execute` method on its root expression which then
// under the hood propagates field values to its leafs by recursively calling
// their `execute` methods and aggregating results into a single boolean value
// as recursion unwinds.
pub(crate) struct CompiledOneExpr<'s>(Box<dyn for<'e> Fn(&'e ExecutionContext<'e>) -> bool + 's>);

impl<'s> CompiledOneExpr<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(closure: impl for<'e> Fn(&'e ExecutionContext<'e>) -> bool + 's) -> Self {
        CompiledOneExpr(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> bool {
        self.0(ctx)
    }
}

type CompiledVecExprResult = Box<[bool]>;

pub(crate) struct CompiledVecExpr<'s>(
    Box<dyn for<'e> Fn(&'e ExecutionContext<'e>) -> CompiledVecExprResult + 's>,
);

impl<'s> CompiledVecExpr<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e>) -> CompiledVecExprResult + 's,
    ) -> Self {
        CompiledVecExpr(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> CompiledVecExprResult {
        self.0(ctx)
    }
}

pub(crate) enum CompiledExpr<'s> {
    One(CompiledOneExpr<'s>),
    Vec(CompiledVecExpr<'s>),
}

impl<'s> CompiledExpr<'s> {
    #[cfg(test)]
    pub fn execute_one<'e>(&self, ctx: &'e ExecutionContext<'e>) -> bool {
        match self {
            CompiledExpr::One(one) => one.execute(ctx),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    #[cfg(test)]
    pub fn execute_vec<'e>(&self, ctx: &'e ExecutionContext<'e>) -> CompiledVecExprResult {
        match self {
            CompiledExpr::One(_) => unreachable!(),
            CompiledExpr::Vec(vec) => vec.execute(ctx),
        }
    }
}

pub(crate) type CompiledValueResult<'a> = Result<LhsValue<'a>, Type>;

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

pub(crate) struct CompiledValueExpr<'s>(
    Box<dyn for<'e> Fn(&'e ExecutionContext<'e>) -> CompiledValueResult<'e> + 's>,
);

impl<'s> CompiledValueExpr<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e>) -> CompiledValueResult<'e> + 's,
    ) -> Self {
        CompiledValueExpr(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> CompiledValueResult<'e> {
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
pub struct Filter<'s> {
    root_expr: CompiledOneExpr<'s>,
    scheme: &'s Scheme,
}

impl<'s> Filter<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledOneExpr<'s>, scheme: &'s Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a filter against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> Result<bool, SchemeMismatchError> {
        if self.scheme == ctx.scheme() {
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
