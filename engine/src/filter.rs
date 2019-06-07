use crate::{
    execution_context::ExecutionContext,
    scheme::Scheme,
    types::{LhsValue, Type},
};
use failure::Fail;

/// SchemeMismatchError occurs when the filter and [`ExecutionContext`] have
/// different [schemes](struct@Scheme).
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "execution context doesn't match the scheme with which filter was parsed")]
pub struct SchemeMismatchError;

/// CompiledExpr is a compiled expression. An expression can compile into either
/// variant of CompiledExpr, depending on the node and it's place in the AST.
pub(crate) enum CompiledExpr<'s> {
    /// The expression returns either true or false.
    BoolExpr(CompiledBoolExpr<'s>),
    /// The expression returns a slice of true or false.
    ///
    /// An example of a BoolVecExpr would be when comparing the elements of
    /// two or more arrays or comparing each element of an array against an RhsValue.
    BoolVecExpr(CompiledVecExpr<'s>),
}

impl<'s> CompiledExpr<'s> {
    #[cfg(test)]
    pub fn execute_one<'e>(&self, ctx: &'e ExecutionContext<'e>) -> bool {
        match self {
            CompiledExpr::BoolExpr(expr) => expr.execute(ctx),
            CompiledExpr::BoolVecExpr(_) => unreachable!(),
        }
    }

    #[cfg(test)]
    pub fn execute_vec<'e>(&self, ctx: &'e ExecutionContext<'e>) -> CompiledVecExprResult {
        match self {
            CompiledExpr::BoolExpr(_) => unreachable!(),
            CompiledExpr::BoolVecExpr(expr) => expr.execute(ctx),
        }
    }
}

/// CompiledBoolExpr is a compiled expression which returns either true or false.
pub(crate) struct CompiledBoolExpr<'s>(Box<dyn for<'e> Fn(&'e ExecutionContext<'e>) -> bool + 's>);

impl<'s> CompiledBoolExpr<'s> {
    /// Creates a compiled expression from a generic closure.
    pub(crate) fn new(closure: impl for<'e> Fn(&'e ExecutionContext<'e>) -> bool + 's) -> Self {
        CompiledBoolExpr(Box::new(closure))
    }

    /// Evaluate the expression against the context.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> bool {
        self.0(ctx)
    }
}

/// CompiledVecExprResult is the slice of true or false returned by CompiledVecExpr.
type CompiledVecExprResult = Box<[bool]>;

/// CompiledVecExpr is a compiled expression which returns a slice of true or false.
///
/// An example of a BoolVecExpr would be comparing the elements of two or more
/// arrays or comparing each element of an array against an RhsValue.
pub(crate) struct CompiledVecExpr<'s>(
    Box<dyn for<'e> Fn(&'e ExecutionContext<'e>) -> CompiledVecExprResult + 's>,
);

impl<'s> CompiledVecExpr<'s> {
    /// Creates a compiled expression from a generic closure.
    pub(crate) fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e>) -> CompiledVecExprResult + 's,
    ) -> Self {
        CompiledVecExpr(Box::new(closure))
    }

    /// Evaluate the expression against the context.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> CompiledVecExprResult {
        self.0(ctx)
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
    root_expr: CompiledBoolExpr<'s>,
    scheme: &'s Scheme,
}

impl<'s> Filter<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledBoolExpr<'s>, scheme: &'s Scheme) -> Self {
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
    use super::SchemeMismatchError;
    use crate::execution_context::ExecutionContext;

    #[test]
    fn test_scheme_mismatch() {
        let scheme1 = Scheme! { foo: Int };
        let scheme2 = Scheme! { foo: Int, bar: Int };
        let filter = scheme1.parse("foo == 42").unwrap().compile();
        let ctx = ExecutionContext::new(&scheme2);

        assert_eq!(filter.execute(&ctx), Err(SchemeMismatchError));
    }
}
