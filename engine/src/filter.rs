use crate::{execution_context::ExecutionContext, scheme::Scheme};
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
pub(crate) struct CompiledExpr<'s>(Box<dyn 's + Fn(&ExecutionContext) -> Option<bool> + Sync + Send>);

impl<'s> CompiledExpr<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(closure: impl 's + Fn(&ExecutionContext) -> Option<bool> + Sync + Send) -> Self {
        CompiledExpr(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute(&self, ctx: &ExecutionContext) -> Option<bool> {
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
    root_expr: CompiledExpr<'s>,
    scheme: &'s Scheme,
}

impl<'s> Filter<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledExpr<'s>, scheme: &'s Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a filter against a provided context with values.
    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> Result<Option<bool>, SchemeMismatchError> {
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
    use crate::LhsValue;

    #[test]
    fn test_scheme_mismatch() {
        let scheme1 = Scheme! { foo: Int };
        let scheme2 = Scheme! { foo: Int, bar: Int };
        let filter = scheme1.parse("foo == 42").unwrap().compile();
        let ctx = ExecutionContext::new(&scheme2);

        assert_eq!(filter.execute(&ctx), Err(SchemeMismatchError));
    }

    #[test]
    fn test_filter_against_present_value_1() {
        let scheme = Scheme! { foo: Int, bar: Int };
        let filter = scheme.parse("bar == 41").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("bar", LhsValue::Int(41)).unwrap();
        assert_eq!(filter.execute(&ctx), Ok(Some(true)));
    }

    #[test]
    fn test_filter_against_missing_value_1() {
        let scheme = Scheme! { foo: Int, bar: Int };
        let filter = scheme.parse("bar == 41").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("foo", LhsValue::Int(41)).unwrap();
        assert_eq!(filter.execute(&ctx), Ok(None));
    }
    #[test]
    fn test_filter_against_missing_value_2() {
        let scheme = Scheme! { foo: Int, bar: Int };
        let filter = scheme.parse("foo == 41").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("bar", LhsValue::Int(41)).unwrap();
        assert_eq!(filter.execute(&ctx), Ok(None));
    }
    #[test]
    fn test_filter_against_ooo_value() {
        let scheme = Scheme! { foo: Int, bar: Int };
        let filter = scheme.parse("bar == 41 && foo == 52").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("foo", LhsValue::Int(52)).unwrap();
        ctx.set_field_value("bar", LhsValue::Int(41)).unwrap();
        assert_eq!(filter.execute(&ctx), Ok(Some(true)));
    }

    #[test]
    fn test_filter_against_or_value() {
        let scheme = Scheme! { foo: Int, bar: Int };
        let filter = scheme.parse("bar == 41 || foo == 52").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("foo", LhsValue::Int(52)).unwrap();
        assert_eq!(filter.execute(&ctx), Ok(Some(true)));
    }

    #[test]
    fn ensure_send_and_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        is_send::<Filter>();
        is_sync::<Filter>();
    }
}
