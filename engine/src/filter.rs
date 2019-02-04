use execution_context::ExecutionContext;

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
pub struct Filter<'s>(Box<dyn 's + Fn(&ExecutionContext<'s>) -> bool>);

impl<'s> Filter<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(closure: impl 's + Fn(&ExecutionContext<'s>) -> bool) -> Self {
        Filter(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        self.0(ctx)
    }
}
