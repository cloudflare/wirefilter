//! Each AST expression node gets compiled into a CompiledExpr or a CompiledValueExpr.
//! Therefore, Filter essentialy is a public API facade for a tree of Compiled(Value)Exprs.
//! When filter gets executed it calls `execute` method on its root expression which then
//! under the hood propagates field values to its leafs by recursively calling
//! their `execute` methods and aggregating results into a single boolean value
//! as recursion unwinds.

use crate::ast::logical_expr::QuantifierOp;
use crate::execution_context::ExecutionContext;
use crate::lhs_types::TypedArray;
use crate::scheme::{Scheme, SchemeMismatchError};
use crate::types::{LhsValue, Type};
use std::fmt;

type BoxedClosureToOneBool<U> =
    Box<dyn for<'e> Fn(&'e ExecutionContext<'e, U>) -> bool + Sync + Send + 'static>;

/// Boxed closure for [`crate::Expr`] AST node that evaluates to a simple [`bool`].
pub struct CompiledOneExpr<U = ()>(BoxedClosureToOneBool<U>);

impl<U> fmt::Debug for CompiledOneExpr<U> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("CompiledOneExpr")
            .field(&((&*self.0) as *const _))
            .finish()
    }
}

impl<U> CompiledOneExpr<U> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e, U>) -> bool + Sync + Send + 'static,
    ) -> Self {
        CompiledOneExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e, U>) -> bool {
        self.0(ctx)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToOneBool<U> {
        self.0
    }
}

pub(crate) type CompiledVecExprResult = TypedArray<'static, bool>;

type BoxedClosureToVecBool<U> = Box<
    dyn for<'e> Fn(&'e ExecutionContext<'e, U>) -> CompiledVecExprResult + Sync + Send + 'static,
>;

type BoolIter<'a> = Box<dyn Iterator<Item = bool> + 'a>;

// Unlike Fn, this trait allows returned iterators to borrow the compiled node.
trait BoolIterExpr<U>: Send + Sync {
    fn execute_iter<'a>(&'a self, ctx: &'a ExecutionContext<'a, U>) -> BoolIter<'a>;
    fn reduce(&self, ctx: &ExecutionContext<'_, U>, op: QuantifierOp) -> bool;
    fn into_boxed_closure(self: Box<Self>) -> BoxedClosureToVecBool<U>;
}

/// Boxed closure for [`crate::Expr`] AST node that evaluates to a list of [`bool`].
pub struct CompiledVecExpr<U = ()>(VecExprImpl<U>);

enum VecExprImpl<U> {
    Eager(BoxedClosureToVecBool<U>),
    Lazy(Box<dyn BoolIterExpr<U>>),
}

impl<U> fmt::Debug for CompiledVecExpr<U> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("CompiledVecExpr")
            .field(&(&self.0 as *const _))
            .finish()
    }
}

impl<U> CompiledVecExpr<U> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e, U>) -> CompiledVecExprResult
        + Sync
        + Send
        + 'static,
    ) -> Self {
        Self(VecExprImpl::Eager(Box::new(closure)))
    }

    // Keep the public array API, but allow reductions to consume elements directly.
    // Boxing here is a prototype tradeoff: allocations scale with expression size,
    // rather than input length, at the cost of dynamic dispatch per element.
    pub(crate) fn new_iter<T: Send + Sync + 'static>(
        data: T,
        make_iter: impl for<'a> Fn(&'a T, &'a ExecutionContext<'a, U>) -> BoolIter<'a>
        + Send
        + Sync
        + 'static,
    ) -> Self {
        Self::new_iter_with_reduce(
            (data, make_iter),
            |(data, make_iter), ctx| make_iter(data, ctx),
            |(data, make_iter), ctx, op| op.reduce_bool_iter(make_iter(data, ctx)),
        )
    }

    // A fused reduction runs on a concrete iterator inside the compiled node,
    // avoiding the iterator box and per-element virtual calls for quantifiers.
    pub(crate) fn new_iter_with_reduce<T: Send + Sync + 'static>(
        data: T,
        make_iter: impl for<'a> Fn(&'a T, &'a ExecutionContext<'a, U>) -> BoolIter<'a>
        + Send
        + Sync
        + 'static,
        reduce: impl for<'a> Fn(&'a T, &'a ExecutionContext<'a, U>, QuantifierOp) -> bool
        + Send
        + Sync
        + 'static,
    ) -> Self {
        struct IterExpr<T, F, R>(T, F, R);
        impl<U, T: Send + Sync + 'static, F, R> BoolIterExpr<U> for IterExpr<T, F, R>
        where
            F: for<'a> Fn(&'a T, &'a ExecutionContext<'a, U>) -> BoolIter<'a>
                + Send
                + Sync
                + 'static,
            R: for<'a> Fn(&'a T, &'a ExecutionContext<'a, U>, QuantifierOp) -> bool
                + Send
                + Sync
                + 'static,
        {
            fn execute_iter<'a>(&'a self, ctx: &'a ExecutionContext<'a, U>) -> BoolIter<'a> {
                (self.1)(&self.0, ctx)
            }

            fn reduce(&self, ctx: &ExecutionContext<'_, U>, op: QuantifierOp) -> bool {
                (self.2)(&self.0, ctx, op)
            }

            fn into_boxed_closure(self: Box<Self>) -> BoxedClosureToVecBool<U> {
                Box::new(move |ctx| self.execute_iter(ctx).collect())
            }
        }
        Self(VecExprImpl::Lazy(Box::new(IterExpr(
            data, make_iter, reduce,
        ))))
    }

    pub(crate) fn reduce(&self, ctx: &ExecutionContext<'_, U>, op: QuantifierOp) -> bool {
        match &self.0 {
            VecExprImpl::Eager(closure) => op.reduce_bool_iter(
                crate::lhs_types::Array::from(closure(ctx))
                    .into_iter()
                    .map(|value| bool::try_from(value).unwrap()),
            ),
            VecExprImpl::Lazy(expr) => expr.reduce(ctx, op),
        }
    }

    pub(crate) fn execute_iter<'a>(&'a self, ctx: &'a ExecutionContext<'a, U>) -> BoolIter<'a> {
        match &self.0 {
            VecExprImpl::Eager(closure) => Box::new(
                crate::lhs_types::Array::from(closure(ctx))
                    .into_iter()
                    .map(|value| bool::try_from(value).unwrap()),
            ),
            VecExprImpl::Lazy(expr) => expr.execute_iter(ctx),
        }
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e, U>) -> CompiledVecExprResult {
        match &self.0 {
            VecExprImpl::Eager(closure) => closure(ctx),
            VecExprImpl::Lazy(expr) => expr.execute_iter(ctx).collect(),
        }
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToVecBool<U> {
        match self.0 {
            VecExprImpl::Eager(closure) => closure,
            VecExprImpl::Lazy(expr) => expr.into_boxed_closure(),
        }
    }
}

/// Enum of boxed closure for [`crate::Expr`] AST nodes.
#[derive(Debug)]
pub enum CompiledExpr<U = ()> {
    /// Variant for [`crate::Expr`] AST node that evaluates to a simple [`bool`].
    One(CompiledOneExpr<U>),
    /// Variant for [`crate::Expr`] AST node that evaluates to a list of [`bool`].
    Vec(CompiledVecExpr<U>),
}

impl<U> CompiledExpr<U> {
    #[cfg(test)]
    pub(crate) fn execute_one<'e>(&self, ctx: &'e ExecutionContext<'e, U>) -> bool {
        match self {
            CompiledExpr::One(one) => one.execute(ctx),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    #[cfg(test)]
    pub(crate) fn execute_vec<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
    ) -> CompiledVecExprResult {
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

impl From<Type> for CompiledValueResult<'_> {
    fn from(ty: Type) -> Self {
        Err(ty)
    }
}

type BoxedClosureToValue<U> = Box<
    dyn for<'e> Fn(&'e ExecutionContext<'e, U>) -> CompiledValueResult<'e> + Sync + Send + 'static,
>;

/// Boxed closure for [`crate::ValueExpr`] AST node that evaluates to an [`LhsValue`].
pub struct CompiledValueExpr<U = ()>(BoxedClosureToValue<U>);

impl<U> fmt::Debug for CompiledValueExpr<U> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("CompiledValueExpr")
            .field(&((&*self.0) as *const _))
            .finish()
    }
}

impl<U> CompiledValueExpr<U> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'e> Fn(&'e ExecutionContext<'e, U>) -> CompiledValueResult<'e>
        + Sync
        + Send
        + 'static,
    ) -> Self {
        CompiledValueExpr(Box::new(closure))
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'e>(&self, ctx: &'e ExecutionContext<'e, U>) -> CompiledValueResult<'e> {
        self.0(ctx)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToValue<U> {
        self.0
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
pub struct Filter<U = ()> {
    root_expr: CompiledOneExpr<U>,
    scheme: Scheme,
}

impl<U> std::fmt::Debug for Filter<U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Filter")
            .field("root", &self.root_expr)
            .field("scheme", &self.scheme)
            .finish()
    }
}

impl<U> Filter<U> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledOneExpr<U>, scheme: Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a compiled filter expression against a provided context with values.
    pub fn execute<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
    ) -> Result<bool, SchemeMismatchError> {
        if ctx.scheme() == &self.scheme {
            Ok(self.root_expr.execute(ctx))
        } else {
            Err(SchemeMismatchError)
        }
    }
}

/// An IR for a compiled value expression.
pub struct FilterValue<U = ()> {
    root_expr: CompiledValueExpr<U>,
    scheme: Scheme,
}

impl<U> FilterValue<U> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledValueExpr<U>, scheme: Scheme) -> Self {
        FilterValue { root_expr, scheme }
    }

    /// Executes a compiled value expression against a provided context with values.
    pub fn execute<'e>(
        &self,
        ctx: &'e ExecutionContext<'e, U>,
    ) -> Result<Result<LhsValue<'e>, Type>, SchemeMismatchError> {
        if ctx.scheme() == &self.scheme {
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
        let scheme1 = Scheme! { foo: Int }.build();
        let scheme2 = Scheme! { foo: Int, bar: Int }.build();
        let filter = scheme1.parse("foo == 42").unwrap().compile();
        let ctx = ExecutionContext::new(&scheme2);

        assert_eq!(filter.execute(&ctx), Err(SchemeMismatchError));
    }

    #[test]
    fn ensure_send_and_sync() {
        fn is_send<T: Send>() {}
        fn is_sync<T: Sync>() {}

        is_send::<Filter<ExecutionContext<'_>>>();
        is_sync::<Filter<ExecutionContext<'_>>>();
    }
}

#[cfg(test)]
mod lazy_vec_tests {
    use super::*;

    #[test]
    fn fused_reduction_does_not_construct_a_boxed_iterator() {
        let scheme = crate::SchemeBuilder::new().build();
        let ctx = ExecutionContext::<()>::new(&scheme);
        let fused = CompiledVecExpr::new_iter_with_reduce(
            [true, false],
            |_, _| panic!("fused quantifiers must not request a boxed iterator"),
            |values, _, op| op.reduce_bool_iter(values.iter().copied()),
        );
        assert!(fused.reduce(&ctx, QuantifierOp::Any));
        assert!(!fused.reduce(&ctx, QuantifierOp::All));
    }

    #[test]
    fn iterator_nodes_preserve_the_array_api() {
        let scheme = crate::SchemeBuilder::new().build();
        let ctx = ExecutionContext::<()>::new(&scheme);
        let lazy = CompiledVecExpr::new_iter((), |(), _| Box::new([true, false].into_iter()));
        assert_eq!(lazy.execute(&ctx), [true, false]);
        assert_eq!(lazy.into_boxed_closure()(&ctx), [true, false]);

        let eager = CompiledVecExpr::new(|_| [true, false].into_iter().collect());
        assert_eq!(eager.execute_iter(&ctx).collect::<Vec<_>>(), [true, false]);
        assert_eq!(eager.into_boxed_closure()(&ctx), [true, false]);
    }
}
