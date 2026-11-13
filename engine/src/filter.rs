//! Each AST expression node gets compiled into a CompiledExpr or a CompiledValueExpr.
//! Therefore, Filter essentialy is a public API facade for a tree of Compiled(Value)Exprs.
//! When filter gets executed it calls `execute` method on its root expression which then
//! under the hood propagates field values to its leafs by recursively calling
//! their `execute` methods and aggregating results into a single boolean value
//! as recursion unwinds.

use crate::context::{ContextFamily, ContextRef, ExecutionContextFamily, HasScheme};
use crate::lhs_types::TypedArray;
use crate::scheme::{Scheme, SchemeMismatchError};
use crate::types::{LhsValue, Type};
use std::fmt;
use std::marker::PhantomData;

type BoxedClosureToOneBool<F> = Box<
    dyn for<'ctx, 'data> Fn(&'ctx <F as ContextFamily>::Context<'data>) -> bool
        + Sync
        + Send
        + 'static,
>;

/// Boxed closure for [`crate::Expr`] AST node that evaluates to a simple [`bool`].
pub struct CompiledOneExpr<U = (), F: ContextFamily<UserData = U> = ExecutionContextFamily<U>>(
    BoxedClosureToOneBool<F>,
    PhantomData<fn() -> U>,
);

impl<U, F: ContextFamily<UserData = U>> fmt::Debug for CompiledOneExpr<U, F> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("CompiledOneExpr")
            .field(&((&*self.0) as *const _))
            .finish()
    }
}

impl<U, F: ContextFamily<UserData = U>> CompiledOneExpr<U, F> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'ctx, 'data> Fn(&'ctx <F as ContextFamily>::Context<'data>) -> bool
        + Sync
        + Send
        + 'static,
    ) -> Self {
        CompiledOneExpr(Box::new(closure), PhantomData)
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'ctx, 'data: 'ctx>(&self, ctx: &'ctx F::Context<'data>) -> bool {
        self.0(ctx)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToOneBool<F> {
        self.0
    }
}

pub(crate) type CompiledVecExprResult = TypedArray<'static, bool>;

type BoxedClosureToVecBool<F> = Box<
    dyn for<'ctx, 'data> Fn(&'ctx <F as ContextFamily>::Context<'data>) -> CompiledVecExprResult
        + Sync
        + Send
        + 'static,
>;

/// Boxed closure for [`crate::Expr`] AST node that evaluates to a list of [`bool`].
pub struct CompiledVecExpr<U = (), F: ContextFamily<UserData = U> = ExecutionContextFamily<U>>(
    BoxedClosureToVecBool<F>,
    PhantomData<fn() -> U>,
);

impl<U, F: ContextFamily<UserData = U>> fmt::Debug for CompiledVecExpr<U, F> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("CompiledVecExpr")
            .field(&((&*self.0) as *const _))
            .finish()
    }
}

impl<U, F: ContextFamily<UserData = U>> CompiledVecExpr<U, F> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'ctx, 'data> Fn(
            &'ctx <F as ContextFamily>::Context<'data>,
        ) -> CompiledVecExprResult
        + Sync
        + Send
        + 'static,
    ) -> Self {
        CompiledVecExpr(Box::new(closure), PhantomData)
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'ctx, 'data: 'ctx>(
        &self,
        ctx: &'ctx F::Context<'data>,
    ) -> CompiledVecExprResult {
        self.0(ctx)
    }

    /// Extracts the underlying boxed closure.
    pub fn into_boxed_closure(self) -> BoxedClosureToVecBool<F> {
        self.0
    }
}

/// Enum of boxed closure for [`crate::Expr`] AST nodes.
pub enum CompiledExpr<U = (), F: ContextFamily<UserData = U> = ExecutionContextFamily<U>> {
    /// Variant for [`crate::Expr`] AST node that evaluates to a simple [`bool`].
    One(CompiledOneExpr<U, F>),
    /// Variant for [`crate::Expr`] AST node that evaluates to a list of [`bool`].
    Vec(CompiledVecExpr<U, F>),
}

impl<U, F: ContextFamily<UserData = U>> fmt::Debug for CompiledExpr<U, F> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::One(expr) => fmt.debug_tuple("One").field(expr).finish(),
            Self::Vec(expr) => fmt.debug_tuple("Vec").field(expr).finish(),
        }
    }
}

impl<U, F: ContextFamily<UserData = U>> CompiledExpr<U, F> {
    #[cfg(test)]
    pub(crate) fn execute_one<'ctx, 'data: 'ctx>(&self, ctx: &'ctx F::Context<'data>) -> bool {
        match self {
            CompiledExpr::One(one) => one.execute(ctx),
            CompiledExpr::Vec(_) => unreachable!(),
        }
    }

    #[cfg(test)]
    pub(crate) fn execute_vec<'ctx, 'data: 'ctx>(
        &self,
        ctx: &'ctx F::Context<'data>,
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

type BoxedClosureToValue<F> = Box<
    dyn for<'ctx, 'data> Fn(ContextRef<'ctx, 'data, F>) -> CompiledValueResult<'ctx>
        + Sync
        + Send
        + 'static,
>;

type BoxedStoredClosureToValue<U> = Box<
    dyn for<'e> Fn(&'e crate::ExecutionContext<'e, U>) -> CompiledValueResult<'e> + Sync + Send,
>;

/// Boxed closure for [`crate::ValueExpr`] AST node that evaluates to an [`LhsValue`].
pub struct CompiledValueExpr<U = (), F: ContextFamily<UserData = U> = ExecutionContextFamily<U>>(
    BoxedClosureToValue<F>,
    PhantomData<fn() -> U>,
);

impl<U, F: ContextFamily<UserData = U>> fmt::Debug for CompiledValueExpr<U, F> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_tuple("CompiledValueExpr")
            .field(&((&*self.0) as *const _))
            .finish()
    }
}

impl<U, F: ContextFamily<UserData = U>> CompiledValueExpr<U, F> {
    /// Creates a compiled expression IR from a generic closure.
    pub fn new(
        closure: impl for<'ctx, 'data> Fn(
            &'ctx <F as ContextFamily>::Context<'data>,
        ) -> CompiledValueResult<'ctx>
        + Sync
        + Send
        + 'static,
    ) -> Self {
        Self::new_with_context(move |ctx| closure(ctx.context()))
    }

    /// Create a value expression that can borrow native context payloads.
    ///
    /// The callback's witness records that the context's retained data outlives
    /// this evaluation. Call [`ContextRef::context`] to obtain the original
    /// context reference before invoking native getters or child expressions.
    pub fn new_with_context(
        closure: impl for<'ctx, 'data> Fn(ContextRef<'ctx, 'data, F>) -> CompiledValueResult<'ctx>
        + Sync
        + Send
        + 'static,
    ) -> Self {
        CompiledValueExpr(Box::new(closure), PhantomData)
    }

    /// Executes the closure against a provided context with values.
    pub fn execute<'ctx, 'data: 'ctx>(
        &self,
        ctx: &'ctx F::Context<'data>,
    ) -> CompiledValueResult<'ctx> {
        self.0(ContextRef::new(ctx))
    }

    /// Extract the callback, retaining its context-lifetime witness.
    pub fn into_boxed_context_closure(self) -> BoxedClosureToValue<F> {
        self.0
    }
}

impl<U: 'static> CompiledValueExpr<U> {
    /// Convert to a callback accepting the ordinary stored execution context.
    ///
    /// This compatibility adapter adds one boxed closure around the expression.
    /// [`Self::into_boxed_context_closure`] extracts the original callback directly.
    pub fn into_boxed_closure(self) -> BoxedStoredClosureToValue<U> {
        Box::new(move |ctx| self.execute(ctx))
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
pub struct Filter<U = (), F: ContextFamily<UserData = U> = ExecutionContextFamily<U>> {
    root_expr: CompiledOneExpr<U, F>,
    scheme: Scheme,
}

impl<U, F: ContextFamily<UserData = U>> std::fmt::Debug for Filter<U, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Filter")
            .field("root", &self.root_expr)
            .field("scheme", &self.scheme)
            .finish()
    }
}

impl<U, F: ContextFamily<UserData = U>> Filter<U, F> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledOneExpr<U, F>, scheme: Scheme) -> Self {
        Filter { root_expr, scheme }
    }

    /// Executes a compiled filter expression against a provided context with values.
    pub fn execute<'ctx, 'data: 'ctx>(
        &self,
        ctx: &'ctx F::Context<'data>,
    ) -> Result<bool, SchemeMismatchError> {
        if ctx.scheme() == &self.scheme {
            Ok(self.root_expr.execute(ctx))
        } else {
            Err(SchemeMismatchError)
        }
    }
}

/// An IR for a compiled value expression.
pub struct FilterValue<U = (), F: ContextFamily<UserData = U> = ExecutionContextFamily<U>> {
    root_expr: CompiledValueExpr<U, F>,
    scheme: Scheme,
}

impl<U, F: ContextFamily<UserData = U>> FilterValue<U, F> {
    /// Creates a compiled expression IR from a generic closure.
    pub(crate) fn new(root_expr: CompiledValueExpr<U, F>, scheme: Scheme) -> Self {
        FilterValue { root_expr, scheme }
    }

    /// Executes a compiled value expression against a provided context with values.
    pub fn execute<'ctx, 'data: 'ctx>(
        &self,
        ctx: &'ctx F::Context<'data>,
    ) -> Result<Result<LhsValue<'ctx>, Type>, SchemeMismatchError> {
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

    #[test]
    fn test_distinct_context_and_data_lifetimes() {
        use crate::{
            CompiledOneExpr, CompiledValueExpr, ContextFamily, EvaluationContext, Field,
            FieldBindingError, FieldConsumer, HasScheme, LhsValue, ListMatcher, ListRef, Scheme,
        };
        use std::cell::Cell;

        struct Context<'data> {
            scheme: &'data Scheme,
            value: Cell<&'data str>,
        }

        impl HasScheme for Context<'_> {
            fn scheme(&self) -> &Scheme {
                self.scheme
            }
        }

        impl EvaluationContext for Context<'_> {
            type UserData = ();

            fn get_user_data(&self) -> &() {
                &()
            }

            fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
                unreachable!("the test scheme has no lists")
            }
        }

        struct Family;

        impl ContextFamily for Family {
            type Context<'data> = Context<'data>;
            type UserData = ();

            fn bind<B: FieldConsumer<Self>>(
                field: Field,
                _: B,
            ) -> Result<B::Output, FieldBindingError> {
                Err(FieldBindingError::UnknownField(field.name().into()))
            }
        }

        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<CompiledValueExpr<(), Family>>();
        assert_send_sync::<CompiledOneExpr<(), Family>>();

        let value =
            CompiledValueExpr::<(), Family>::new(|ctx| Ok(LhsValue::Bytes(ctx.value.get().into())));
        let matches = CompiledOneExpr::<(), Family>::new(|ctx| ctx.value.get() == "first");
        let first = String::from("first");
        let second = String::from("second");
        let scheme = crate::SchemeBuilder::new().build();
        let mut ctx = Context {
            scheme: &scheme,
            value: Cell::new(&first),
        };
        assert_eq!(value.execute(&ctx).unwrap(), LhsValue::from("first"));
        assert!(matches.execute(&ctx));
        *ctx.value.get_mut() = &second;
        assert_eq!(value.execute(&ctx).unwrap(), LhsValue::from("second"));
        assert!(!matches.execute(&ctx));
    }
}
