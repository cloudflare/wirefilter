use execution_context::ExecutionContext;
use failure::Fail;
use scheme::Scheme;

/// An error that occurs if filter and provided [`ExecutionContext`] have
/// different [schemes](`Scheme`).
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "Tried to execute filter parsed with a different scheme.")]
pub struct SchemeMismatchError;

pub(crate) struct CompiledExpr<'s>(Box<dyn 's + Fn(&ExecutionContext<'s>) -> bool>);

impl<'s> CompiledExpr<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(closure: impl 's + Fn(&ExecutionContext<'s>) -> bool) -> Self {
        CompiledExpr(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
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
    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> Result<bool, SchemeMismatchError> {
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
    use execution_context::ExecutionContext;
    use scheme::Scheme;
    use types::Type;

    macro_rules! create_scheme {
        ($fields:expr) => {
            Scheme::from($fields.iter().map(|&(k, t)| (k.to_owned(), t)).collect())
        };
    }

    #[test]
    fn test_scheme_mismatch() {
        let scheme1 = create_scheme!(&[("foo", Type::Int)]);
        let scheme2 = create_scheme!(&[("foo", Type::Int), ("bar", Type::Int)]);
        let filter = scheme1.parse("foo == 42").unwrap().compile();
        let ctx = ExecutionContext::new(&scheme2);

        assert_eq!(filter.execute(&ctx), Err(SchemeMismatchError));
    }
}
