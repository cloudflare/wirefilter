mod combined_expr;
mod field_expr;
mod simple_expr;

use self::combined_expr::CombinedExpr;
use execution_context::ExecutionContext;
use lex::{LexResult, LexWith};
use scheme::{Field, Scheme, UnknownFieldError};
use serde::Serialize;
use std::fmt::{self, Debug};

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
pub struct CompiledExpr<'s>(Box<dyn 's + Fn(&ExecutionContext<'s>) -> bool>);

impl<'s> CompiledExpr<'s> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(closure: impl 's + Fn(&ExecutionContext<'s>) -> bool) -> Self {
        CompiledExpr(Box::new(closure))
    }

    /// Executes a filter against a provided context with values.
    pub fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        self.0(ctx)
    }
}

trait Expr<'s>: Sized + Eq + Debug + for<'i> LexWith<'i, &'s Scheme> + Serialize {
    fn uses(&self, field: Field<'s>) -> bool;
    fn compile(self) -> CompiledExpr<'s>;
}

/// A parsed filter AST.
///
/// It's attached to its corresponding [`Scheme`] because all parsed fields
/// are represented as indices and are valid only when [`ExecutionContext`]
/// is created from the same scheme.
#[derive(PartialEq, Eq, Serialize, Clone)]
#[serde(transparent)]
pub struct Filter<'s> {
    #[serde(skip)]
    scheme: &'s Scheme,

    op: CombinedExpr<'s>,
}

impl<'s> Debug for Filter<'s> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.op.fmt(f)
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for Filter<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (op, input) = CombinedExpr::lex_with(input, scheme)?;
        Ok((Filter { scheme, op }, input))
    }
}

impl<'s> Filter<'s> {
    /// Recursively checks whether a [`Filter`] uses a given field name.
    ///
    /// This is useful to lazily initialise expensive fields only if necessary.
    pub fn uses(&self, field_name: &str) -> Result<bool, UnknownFieldError> {
        self.scheme
            .get_field_index(field_name)
            .map(|field| self.op.uses(field))
    }

    /// Compiles a [`Filter`] into a compiled expression IR.
    pub fn compile(self) -> CompiledExpr<'s> {
        let scheme = self.scheme;
        let op = self.op.compile();

        CompiledExpr::new(move |ctx| {
            if scheme != ctx.scheme() {
                panic!("Tried to execute filter parsed with a different scheme.");
            }

            op.execute(ctx)
        })
    }
}
