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
    root_expr: CompiledValueExpr<'s>,
    scheme: &'s Scheme,
}

impl<'s> Filter<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledValueExpr<'s>, scheme: &'s Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a filter against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e>) -> Result<bool, SchemeMismatchError> {
        if self.scheme == ctx.scheme() {
            match self.root_expr.execute(ctx) {
                Ok(LhsValue::Bool(b)) => Ok(b),
                /// TODO: remove unwrap
                _ => panic!(""),
            }
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
