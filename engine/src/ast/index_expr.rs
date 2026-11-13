use super::ValueExpr;
use super::field_expr::IdentifierExpr;
use super::parse::FilterParser;
use super::visitor::{Visitor, VisitorMut};
#[cfg(test)]
use crate::ExecutionContext;
use crate::Field;
use crate::compiler::Compiler;
use crate::context::{
    ContextFamily, FieldBindingError, FieldConsumer, FieldGetter, ProviderFamily,
    StoredContextFamily,
};
use crate::filter::{CompiledExpr, CompiledOneExpr, CompiledValueExpr, CompiledVecExpr};
use crate::lex::{Lex, LexErrorKind, LexResult, LexWith, expect, skip_space, span};
use crate::lhs_types::{Array, Map, TypedArray};
use crate::native::values::{self, FieldValueType, IntoLhsValue, NativePredicate, NativeValue};
use crate::scheme::{FieldIndex, IndexAccessError};
use crate::types::{GetType, IntoIter, LhsValue, Type};
use serde::ser::SerializeSeq;
use serde::{Serialize, Serializer};
use std::net::IpAddr;

const BOOL_ARRAY: TypedArray<'_, bool> = TypedArray::new();

/// IndexExpr is an expr that destructures an index into an IdentifierExpr.
///
/// For example, given a scheme which declares a field `http.request.headers`,
/// as a map of string to list of strings, then the expression
/// `http.request.headers["Cookie"][0]` would have an IdentifierExpr
/// of `http.request.headers` and indexes `["Cookie", 0]`.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct IndexExpr {
    /// The accessed identifier.
    pub identifier: IdentifierExpr,
    /// The list of indexes access.
    pub indexes: Box<[FieldIndex]>,
}

#[allow(clippy::manual_ok_err)]
#[inline]
pub fn ok_ref<T, E>(result: &Result<T, E>) -> Option<&T> {
    match result {
        Ok(x) => Some(x),
        Err(_) => None,
    }
}

impl ValueExpr for IndexExpr {
    #[inline]
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        match self.identifier {
            IdentifierExpr::Field(ref field) => visitor.visit_field(field),
            IdentifierExpr::FunctionCallExpr(ref call) => visitor.visit_function_call_expr(call),
        }
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        match self.identifier {
            IdentifierExpr::Field(ref field) => visitor.visit_field(field),
            IdentifierExpr::FunctionCallExpr(ref mut call) => {
                visitor.visit_function_call_expr(call)
            }
        }
    }

    fn compile_with_compiler<C: Compiler>(
        self,
        compiler: &mut C,
    ) -> CompiledValueExpr<C::U, C::Family> {
        let mut ty = self.get_type();
        let count = self.map_each_count();
        let flatten = match count {
            0 => false,
            1 if self.indexes.last() == Some(&FieldIndex::MapEach) => {
                // Preserve the parent container: a terminal `map[*]` evaluates
                // to a Map here, and mapped-function execution consumes its values.
                // Native maps could instead produce an array of values directly,
                // avoiding map materialization and key copies. That would change
                // the value visible to Compiler hooks wrapping this expression
                // (e.g. compile_index_expr / compile_function_call_arg_expr), so
                // it requires a separate compatibility decision.
                ty = Type::Array(ty.into());
                false
            }
            _ => true,
        };
        let Self {
            identifier,
            indexes,
        } = self;
        // Resolve the terminal `[*]` selection during compilation so the
        // closure owns only the indices it follows, without a separate end offset.
        let indexes = if flatten {
            indexes
        } else {
            simplify_indexes(indexes)
        };
        match identifier {
            IdentifierExpr::Field(field) => compiler
                .bind_field(
                    field,
                    ValueConsumer {
                        indexes,
                        ty,
                        flatten,
                    },
                )
                .expect("field binding or native path preparation failed"),
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                match (flatten, indexes.is_empty()) {
                    (false, true) => call,
                    (false, false) => CompiledValueExpr::new_with_context(move |ctx| {
                        let ctx = ctx.context();
                        call.execute(ctx)
                            .ok()
                            .and_then(|value| value.extract_nested(&indexes))
                            .ok_or(ty)
                    }),
                    (true, _) => {
                        let return_type = Type::Array(ty.into());
                        CompiledValueExpr::new_with_context(move |ctx| {
                            let ctx = ctx.context();
                            let mut iter = MapEachIterator::from_indexes(&indexes);
                            iter.reset(call.execute(ctx).map_err(|_| return_type)?);
                            Ok(LhsValue::Array(Array::try_from_iter(ty, iter).unwrap()))
                        })
                    }
                }
            }
        }
    }
}

fn simplify_indexes(indexes: Box<[FieldIndex]>) -> Box<[FieldIndex]> {
    if Some(&FieldIndex::MapEach) == indexes.last() {
        let mut indexes = indexes.into_vec();
        indexes.pop();
        indexes.into_boxed_slice()
    } else {
        indexes
    }
}

/// Interface used to implement comparison against a value.
pub trait Compare<U: 'static, F: ContextFamily<UserData = U> = StoredContextFamily<U>>:
    Send + Sync + 'static
{
    /// Returns true if the value matches the comparison.
    fn compare<'ctx, 'data: 'ctx>(
        &self,
        value: &LhsValue<'ctx>,
        ctx: &'ctx F::Context<'data>,
    ) -> bool;

    /// Compare native bytes. Override to operate directly on the native value.
    #[inline]
    fn compare_bytes<'ctx, 'data: 'ctx>(
        &self,
        value: &'ctx [u8],
        ctx: &'ctx F::Context<'data>,
    ) -> bool {
        self.compare(&LhsValue::Bytes(value.into()), ctx)
    }
    /// Compare a native integer.
    #[inline]
    fn compare_int<'ctx, 'data: 'ctx>(&self, value: i64, ctx: &'ctx F::Context<'data>) -> bool {
        self.compare(&LhsValue::Int(value), ctx)
    }
    /// Compare a native Boolean.
    #[inline]
    fn compare_bool<'ctx, 'data: 'ctx>(&self, value: bool, ctx: &'ctx F::Context<'data>) -> bool {
        self.compare(&LhsValue::Bool(value), ctx)
    }
    /// Compare a native IP address.
    #[inline]
    fn compare_ip<'ctx, 'data: 'ctx>(&self, value: IpAddr, ctx: &'ctx F::Context<'data>) -> bool {
        self.compare(&LhsValue::Ip(value), ctx)
    }
}

#[inline]
fn required<T>(value: Option<T>, field: &Field) -> Option<T> {
    if value.is_none() && !field.optional() {
        panic!(
            "Field {} was registered as mandatory but not given a value",
            field.name()
        );
    }
    value
}

fn check_native_field<S: FieldValueType>(field: &Field) -> Result<(), FieldBindingError> {
    let expected = field.get_type();
    if let Some(actual) = S::STATIC_TYPE
        && actual != expected
    {
        return Err(FieldBindingError::TypeMismatch {
            field: field.name().into(),
            expected,
            actual,
        });
    }
    Ok(())
}

struct MaterializationCost;

impl<F: ContextFamily> FieldConsumer<F> for MaterializationCost {
    type Output = bool;

    fn native<G: FieldGetter<F>>(self, field: Field, _: G) -> Result<bool, FieldBindingError> {
        // Stored values also use this interface, but borrowing their containers
        // must not introduce the memoization allocation for native conversion.
        Ok(<<G::Provider as ProviderFamily>::Value<'static, 'static> as IntoLhsValue<
                'static,
            >>::MATERIALIZES_COLLECTIONS
            && matches!(field.get_type(), Type::Array(_) | Type::Map(_)))
    }
}

struct ValueConsumer {
    indexes: Box<[FieldIndex]>,
    ty: Type,
    flatten: bool,
}

impl<F: ContextFamily> FieldConsumer<F> for ValueConsumer {
    type Output = CompiledValueExpr<F::UserData, F>;

    fn native<G: FieldGetter<F>>(
        self,
        field: Field,
        getter: G,
    ) -> Result<Self::Output, FieldBindingError> {
        check_native_field::<<G::Provider as ProviderFamily>::ValueType>(&field)?;
        let Self {
            indexes,
            ty,
            flatten,
        } = self;
        Ok(match (flatten, indexes.is_empty()) {
            (false, true) => CompiledValueExpr::new_with_context(move |ctx| {
                let ctx = ctx.context();
                materialize_native_root(getter.get(ctx, &field), &field, ty)
            }),
            (false, false) => CompiledValueExpr::new_with_context(move |ctx| {
                let ctx = ctx.context();
                materialize_native_selection(getter.get(ctx, &field), &field, &indexes, ty)
            }),
            (true, _) => {
                let return_type = Type::Array(ty.into());
                CompiledValueExpr::new_with_context(move |ctx| {
                    let ctx = ctx.context();
                    materialize_native_map_each(
                        getter.get(ctx, &field),
                        &field,
                        &indexes,
                        ty,
                        return_type,
                    )
                })
            }
        })
    }
}

// Each caller already knows whether it needs one result, a flat array, or
// nested `[*]` traversal. Keep that choice in the consumer type so binding
// returns the concrete compiled expression without another mode dispatch.
struct OneComparisonConsumer<P> {
    indexes: Box<[FieldIndex]>,
    default: bool,
    comp: P,
}

struct VecComparisonConsumer<P> {
    indexes: Box<[FieldIndex]>,
    comp: P,
}

struct IterComparisonConsumer<P> {
    indexes: Box<[FieldIndex]>,
    comp: P,
}

struct ContextComparison<'p, 'ctx, 'data, F: ContextFamily, P> {
    comp: &'p P,
    ctx: &'ctx F::Context<'data>,
}

impl<F: ContextFamily, P: Compare<F::UserData, F>> NativePredicate
    for ContextComparison<'_, '_, '_, F, P>
{
    #[inline]
    fn lhs(&self, value: &LhsValue<'_>) -> bool {
        self.comp.compare(value, self.ctx)
    }

    #[inline]
    fn bytes(&self, value: &[u8]) -> bool {
        self.comp.compare_bytes(value, self.ctx)
    }

    #[inline]
    fn int(&self, value: i64) -> bool {
        self.comp.compare_int(value, self.ctx)
    }

    #[inline]
    fn boolean(&self, value: bool) -> bool {
        self.comp.compare_bool(value, self.ctx)
    }

    #[inline]
    fn ip(&self, value: IpAddr) -> bool {
        self.comp.compare_ip(value, self.ctx)
    }
}

// Share type validation and path-type calculation across getter types.
fn native_input_type(field: &Field, depth: usize) -> Type {
    let mut input_type = field.get_type();
    for _ in 0..depth {
        input_type = input_type
            .next()
            .expect("parsed native path must have valid types");
    }
    input_type
}

// Prepare paths independently of getter types.
enum PreparedNativePath<S: FieldValueType> {
    Native(S::Path),
    Collection(Box<[FieldIndex]>),
}

fn prepare_native_path<S: FieldValueType>(
    field: &Field,
    indexes: Box<[FieldIndex]>,
    add_map_each: bool,
) -> Result<PreparedNativePath<S>, FieldBindingError> {
    check_native_field::<S>(field)?;
    let input_type = native_input_type(field, indexes.len() + usize::from(add_map_each));
    if needs_collection_conversion::<S>() && matches!(input_type, Type::Array(_) | Type::Map(_)) {
        return Ok(PreparedNativePath::Collection(indexes));
    }
    let mut indexes = indexes.into_vec();
    if add_map_each {
        indexes.push(FieldIndex::MapEach);
    }
    let path = S::compile_field_path(field.get_type(), indexes, input_type)
        .map_err(|error| FieldBindingError::Unsupported(error.0))?;
    Ok(PreparedNativePath::Native(path))
}

// Preserve the constant guards that prevent scalar providers from instantiating
// collection-conversion helpers. Readers supporting direct collection comparison
// also bypass those helpers.
const fn needs_collection_conversion<S: FieldValueType>() -> bool {
    !S::DIRECT_COLLECTION_COMPARISON
        && matches!(S::STATIC_TYPE, None | Some(Type::Array(_) | Type::Map(_)))
}

// Keep the execute_native_* helpers separate from getter-specific closures.
// Execution depends on the context family, produced value type and comparator,
// not the getter type, so fields with the same types can share execution code
// while their closures retain concrete getter calls. Moving these bodies into
// the closures substantially increased release-build compiler memory and code
// size. Leave inlining decisions to the compiler.
fn execute_native_one<F, V, P>(
    ctx: &F::Context<'_>,
    field: &Field,
    value: Option<V>,
    path: &<V::ValueType as FieldValueType>::Path,
    comp: &P,
    default: bool,
) -> bool
where
    F: ContextFamily,
    V: NativeValue,
    P: Compare<F::UserData, F>,
{
    let Some(value) = required(value, field) else {
        return default;
    };
    let predicate = ContextComparison::<F, _> { comp, ctx };
    values::compare_one(&value, path, &predicate).unwrap_or(default)
}

fn execute_native_vec<F, V, P>(
    ctx: &F::Context<'_>,
    field: &Field,
    value: Option<V>,
    path: &<V::ValueType as FieldValueType>::Path,
    comp: &P,
) -> TypedArray<'static, bool>
where
    F: ContextFamily,
    V: NativeValue,
    P: Compare<F::UserData, F>,
{
    let mut output = TypedArray::new();
    if let Some(value) = required(value, field) {
        let predicate = ContextComparison::<F, _> { comp, ctx };
        values::compare_vec(&value, path, &predicate, &mut output);
    }
    output
}

fn execute_native_collection_one<'ctx, 'data: 'ctx, F, V, P>(
    ctx: &'ctx F::Context<'data>,
    field: &Field,
    value: Option<V>,
    indexes: &[FieldIndex],
    comp: &P,
    default: bool,
) -> bool
where
    F: ContextFamily,
    V: IntoLhsValue<'ctx>,
    P: Compare<F::UserData, F>,
{
    required(value, field)
        .map(IntoLhsValue::into_lhs)
        .as_ref()
        .and_then(|value| value.get_nested(indexes))
        .map_or(default, |value| comp.compare(value, ctx))
}

fn execute_native_collection_vec<'ctx, 'data: 'ctx, F, V, P>(
    ctx: &'ctx F::Context<'data>,
    field: &Field,
    value: Option<V>,
    indexes: &[FieldIndex],
    comp: &P,
) -> TypedArray<'static, bool>
where
    F: ContextFamily,
    V: IntoLhsValue<'ctx>,
    P: Compare<F::UserData, F>,
{
    let value = required(value, field).map(IntoLhsValue::into_lhs);
    value
        .as_ref()
        .and_then(|value| value.get_nested(indexes))
        .map_or(BOOL_ARRAY, |value| {
            TypedArray::from_iter(value.iter().unwrap().map(|item| comp.compare(item, ctx)))
        })
}

fn execute_native_collection_iter<'ctx, 'data: 'ctx, F, V, P>(
    ctx: &'ctx F::Context<'data>,
    field: &Field,
    value: Option<V>,
    indexes: &[FieldIndex],
    comp: &P,
) -> TypedArray<'static, bool>
where
    F: ContextFamily,
    V: IntoLhsValue<'ctx>,
    P: Compare<F::UserData, F>,
{
    let Some(value) = required(value, field) else {
        return TypedArray::default();
    };
    let mut iter = MapEachIterator::from_indexes(indexes);
    iter.reset(value.into_lhs());
    TypedArray::from_iter(iter.map(|item| comp.compare(&item, ctx)))
}

fn materialize_native_root<'ctx, V: IntoLhsValue<'ctx>>(
    value: Option<V>,
    field: &Field,
    ty: Type,
) -> Result<LhsValue<'ctx>, Type> {
    required(value, field).map(IntoLhsValue::into_lhs).ok_or(ty)
}

fn materialize_native_selection<'ctx, V: IntoLhsValue<'ctx>>(
    value: Option<V>,
    field: &Field,
    indexes: &[FieldIndex],
    ty: Type,
) -> Result<LhsValue<'ctx>, Type> {
    required(value, field)
        .and_then(|value| value.into_lhs_at(indexes))
        .ok_or(ty)
}

fn materialize_native_map_each<'ctx, V: IntoLhsValue<'ctx>>(
    value: Option<V>,
    field: &Field,
    indexes: &[FieldIndex],
    ty: Type,
    return_type: Type,
) -> Result<LhsValue<'ctx>, Type> {
    let value = required(value, field).ok_or(return_type)?;
    // Missing children contribute no elements; an absent root remains an error.
    // Only selected values are materialized, retaining terminal map[*] behavior.
    let mut values = Vec::new();
    value.append_lhs_at(indexes, &mut values);
    Ok(LhsValue::Array(Array::try_from_vec(ty, values).unwrap()))
}

// Both vector consumers construct the same small native execution closure.
fn compile_native_vec<F, G, P>(
    field: Field,
    getter: G,
    path: <<G::Provider as ProviderFamily>::ValueType as FieldValueType>::Path,
    comp: P,
) -> CompiledVecExpr<F::UserData, F>
where
    F: ContextFamily,
    G: FieldGetter<F>,
    P: Compare<F::UserData, F>,
{
    CompiledVecExpr::new(move |ctx| {
        execute_native_vec::<F, _, P>(ctx, &field, getter.get(ctx, &field), &path, &comp)
    })
}

impl<F: ContextFamily, P: Compare<F::UserData, F>> FieldConsumer<F> for OneComparisonConsumer<P> {
    type Output = CompiledOneExpr<F::UserData, F>;

    fn native<G: FieldGetter<F>>(
        self,
        field: Field,
        getter: G,
    ) -> Result<Self::Output, FieldBindingError> {
        let Self {
            indexes,
            default,
            comp,
        } = self;
        let prepared = prepare_native_path::<<G::Provider as ProviderFamily>::ValueType>(
            &field, indexes, false,
        )?;
        match prepared {
            PreparedNativePath::Native(path) => Ok(CompiledOneExpr::new(move |ctx| {
                execute_native_one::<F, _, P>(
                    ctx,
                    &field,
                    getter.get(ctx, &field),
                    &path,
                    &comp,
                    default,
                )
            })),
            PreparedNativePath::Collection(indexes) => {
                // Retain the constant root-type guard so scalar providers do not
                // instantiate collection conversion closures behind this boundary.
                if needs_collection_conversion::<<G::Provider as ProviderFamily>::ValueType>() {
                    Ok(CompiledOneExpr::new(move |ctx| {
                        execute_native_collection_one::<F, _, P>(
                            ctx,
                            &field,
                            getter.get(ctx, &field),
                            &indexes,
                            &comp,
                            default,
                        )
                    }))
                } else {
                    unreachable!("provider does not require collection conversion")
                }
            }
        }
    }
}

impl<F: ContextFamily, P: Compare<F::UserData, F>> FieldConsumer<F> for VecComparisonConsumer<P> {
    type Output = CompiledVecExpr<F::UserData, F>;

    fn native<G: FieldGetter<F>>(
        self,
        field: Field,
        getter: G,
    ) -> Result<Self::Output, FieldBindingError> {
        let Self { indexes, comp } = self;
        let prepared = prepare_native_path::<<G::Provider as ProviderFamily>::ValueType>(
            &field, indexes, true,
        )?;
        match prepared {
            PreparedNativePath::Native(path) => {
                Ok(compile_native_vec::<F, G, P>(field, getter, path, comp))
            }
            PreparedNativePath::Collection(indexes) => {
                // Retain the constant root-type guard so scalar providers do not
                // instantiate collection conversion closures behind this boundary.
                if needs_collection_conversion::<<G::Provider as ProviderFamily>::ValueType>() {
                    Ok(CompiledVecExpr::new(move |ctx| {
                        execute_native_collection_vec::<F, _, P>(
                            ctx,
                            &field,
                            getter.get(ctx, &field),
                            &indexes,
                            &comp,
                        )
                    }))
                } else {
                    unreachable!("provider does not require collection conversion")
                }
            }
        }
    }
}

impl<F: ContextFamily, P: Compare<F::UserData, F>> FieldConsumer<F> for IterComparisonConsumer<P> {
    type Output = CompiledVecExpr<F::UserData, F>;

    fn native<G: FieldGetter<F>>(
        self,
        field: Field,
        getter: G,
    ) -> Result<Self::Output, FieldBindingError> {
        let Self { indexes, comp } = self;
        let prepared = prepare_native_path::<<G::Provider as ProviderFamily>::ValueType>(
            &field, indexes, false,
        )?;
        match prepared {
            PreparedNativePath::Native(path) => {
                Ok(compile_native_vec::<F, G, P>(field, getter, path, comp))
            }
            PreparedNativePath::Collection(indexes) => {
                // Retain the constant root-type guard so scalar providers do not
                // instantiate collection conversion closures behind this boundary.
                if needs_collection_conversion::<<G::Provider as ProviderFamily>::ValueType>() {
                    Ok(CompiledVecExpr::new(move |ctx| {
                        execute_native_collection_iter::<F, _, P>(
                            ctx,
                            &field,
                            getter.get(ctx, &field),
                            &indexes,
                            &comp,
                        )
                    }))
                } else {
                    unreachable!("provider does not require collection conversion")
                }
            }
        }
    }
}

impl IndexExpr {
    /// Determine conversion cost while the field's provider type is known.
    pub(crate) fn materializes_native_collection<C: Compiler>(&self, compiler: &mut C) -> bool {
        match &self.identifier {
            // Custom by-value descriptors may still convert before indexing.
            // Conservatively memoize collection-backed arguments even when
            // borrowed native storage can select a scalar without conversion.
            IdentifierExpr::Field(field)
                if matches!(field.get_type(), Type::Array(_) | Type::Map(_)) =>
            {
                compiler
                    .bind_field(field.clone(), MaterializationCost)
                    .expect("field binding or native path preparation failed")
            }
            IdentifierExpr::Field(_) | IdentifierExpr::FunctionCallExpr(_) => false,
        }
    }

    fn compile_one_with<C: Compiler>(
        self,
        compiler: &mut C,
        default: bool,
        comp: impl Compare<C::U, C::Family>,
    ) -> CompiledOneExpr<C::U, C::Family> {
        let Self {
            identifier,
            indexes,
        } = self;
        let indexes = simplify_indexes(indexes);
        match identifier {
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                if indexes.is_empty() {
                    CompiledOneExpr::new(move |ctx| {
                        call.execute(ctx).map_or(
                            default,
                            #[inline]
                            |val| comp.compare(&val, ctx),
                        )
                    })
                } else {
                    CompiledOneExpr::new(move |ctx| {
                        ok_ref(&call.execute(ctx))
                            .and_then(|val| val.get_nested(&indexes))
                            .map_or(
                                default,
                                #[inline]
                                |val| comp.compare(val, ctx),
                            )
                    })
                }
            }
            IdentifierExpr::Field(field) => compiler
                .bind_field(
                    field,
                    OneComparisonConsumer {
                        indexes,
                        default,
                        comp,
                    },
                )
                .expect("field binding or native path preparation failed"),
        }
    }

    pub(crate) fn compile_vec_with<C: Compiler>(
        self,
        compiler: &mut C,
        comp: impl Compare<C::U, C::Family>,
    ) -> CompiledVecExpr<C::U, C::Family> {
        let Self {
            identifier,
            indexes,
        } = self;
        let indexes = simplify_indexes(indexes);
        match identifier {
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                CompiledVecExpr::new(move |ctx| {
                    let comp = &comp;
                    ok_ref(&call.execute(ctx))
                        .and_then(|val| val.get_nested(&indexes))
                        .map_or(
                            BOOL_ARRAY,
                            #[inline]
                            |val: &LhsValue<'_>| {
                                TypedArray::from_iter(
                                    val.iter().unwrap().map(|item| comp.compare(item, ctx)),
                                )
                            },
                        )
                })
            }
            IdentifierExpr::Field(field) => compiler
                .bind_field(field, VecComparisonConsumer { indexes, comp })
                .expect("field binding or native path preparation failed"),
        }
    }

    pub(crate) fn compile_iter_with<C: Compiler>(
        self,
        compiler: &mut C,
        comp: impl Compare<C::U, C::Family>,
    ) -> CompiledVecExpr<C::U, C::Family> {
        let Self {
            identifier,
            indexes,
        } = self;
        match identifier {
            IdentifierExpr::Field(field) => compiler
                .bind_field(field, IterComparisonConsumer { indexes, comp })
                .expect("field binding or native path preparation failed"),
            IdentifierExpr::FunctionCallExpr(call) => {
                let call = compiler.compile_function_call_expr(call);
                CompiledVecExpr::new(move |ctx| {
                    let mut iter = MapEachIterator::from_indexes(&indexes[..]);
                    match call.execute(ctx) {
                        Ok(val) => {
                            iter.reset(val);
                        }
                        _ => {
                            return TypedArray::default();
                        }
                    }

                    TypedArray::from_iter(iter.map(|item| comp.compare(&item, ctx)))
                })
            }
        }
    }

    /// Compiles an [`IndexExpr`] node into a [`CompiledExpr`] (boxed closure) using the
    /// provided comparison function that returns a boolean.
    pub fn compile_with<C: Compiler>(
        self,
        compiler: &mut C,
        default: bool,
        comp: impl Compare<C::U, C::Family>,
    ) -> CompiledExpr<C::U, C::Family> {
        match self.map_each_count() {
            0 => CompiledExpr::One(self.compile_one_with(compiler, default, comp)),
            1 if self.indexes.last() == Some(&FieldIndex::MapEach) => {
                CompiledExpr::Vec(self.compile_vec_with(compiler, comp))
            }
            _ => CompiledExpr::Vec(self.compile_iter_with(compiler, comp)),
        }
    }

    pub(crate) fn map_each_count(&self) -> usize {
        self.indexes
            .iter()
            .filter(|&index| index == &FieldIndex::MapEach)
            .count()
    }

    /// Returns the type produced by evaluating this expression.
    ///
    /// Unlike [`GetType::get_type`], this accounts for `MapEach` accesses. An
    /// expression containing one or more `MapEach` accesses produces a
    /// flattened array of the indexed element type.
    pub(crate) fn output_type(&self) -> Type {
        let ty = self.get_type();
        if self.map_each_count() == 0 {
            ty
        } else {
            Type::Array(ty.into())
        }
    }

    /// Returns the associated identifier (field or function call).
    pub fn identifier(&self) -> &IdentifierExpr {
        &self.identifier
    }

    /// Returns the index accesses as a list of [`FieldIndex`].
    pub fn indexes(&self) -> &[FieldIndex] {
        &self.indexes
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for IndexExpr {
    fn lex_with(mut input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (identifier, rest) = IdentifierExpr::lex_with(input, parser)?;

        let mut current_type = identifier.get_type();

        let mut indexes = Vec::new();

        input = rest;

        while let Ok(rest) = expect(input, "[") {
            let rest = skip_space(rest);

            let (idx, rest) = FieldIndex::lex(rest)?;

            let mut rest = skip_space(rest);

            rest = expect(rest, "]")?;

            match &idx {
                FieldIndex::ArrayIndex(_) => match current_type {
                    Type::Array(array_type) => {
                        current_type = array_type.into();
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ));
                    }
                },
                FieldIndex::MapKey(_) => match current_type {
                    Type::Map(map_type) => {
                        current_type = map_type.into();
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ));
                    }
                },
                FieldIndex::MapEach => match current_type {
                    Type::Array(array_type) => {
                        current_type = array_type.into();
                    }
                    Type::Map(map_type) => {
                        current_type = map_type.into();
                    }
                    _ => {
                        return Err((
                            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                                index: idx,
                                actual: current_type,
                            }),
                            span(input, rest),
                        ));
                    }
                },
            };

            input = rest;

            indexes.push(idx);
        }

        Ok((
            IndexExpr {
                identifier,
                indexes: indexes.into_boxed_slice(),
            },
            input,
        ))
    }
}

impl GetType for IndexExpr {
    fn get_type(&self) -> Type {
        let mut ty = self.identifier.get_type();
        for index in &self.indexes {
            ty = match (ty, index) {
                (Type::Array(sub_ty), FieldIndex::ArrayIndex(_)) => sub_ty.into(),
                (Type::Array(sub_ty), FieldIndex::MapEach) => sub_ty.into(),
                (Type::Map(sub_ty), FieldIndex::MapKey(_)) => sub_ty.into(),
                (Type::Map(sub_ty), FieldIndex::MapEach) => sub_ty.into(),
                (_, _) => unreachable!(),
            }
        }
        ty
    }
}

impl Serialize for IndexExpr {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        if self.indexes.is_empty() {
            self.identifier.serialize(ser)
        } else {
            let mut seq = ser.serialize_seq(Some(self.indexes.len() + 1))?;
            match &self.identifier {
                IdentifierExpr::Field(field) => seq.serialize_element(field)?,
                IdentifierExpr::FunctionCallExpr(call) => seq.serialize_element(call)?,
            };
            for index in &self.indexes {
                seq.serialize_element(index)?;
            }
            seq.end()
        }
    }
}

enum FieldIndexIterator<'a, 'b> {
    ArrayIndex(Option<(Array<'a>, u32)>),
    MapKey(Option<(Map<'a>, &'b [u8])>),
    MapEach(IntoIter<'a>),
}

impl<'a, 'b> FieldIndexIterator<'a, 'b> {
    fn new(val: LhsValue<'a>, idx: &'b FieldIndex) -> Result<Self, IndexAccessError> {
        match idx {
            FieldIndex::ArrayIndex(idx) => match val {
                LhsValue::Array(arr) => Ok(Self::ArrayIndex(Some((arr, *idx)))),
                _ => Err(IndexAccessError {
                    index: FieldIndex::ArrayIndex(*idx),
                    actual: val.get_type(),
                }),
            },
            FieldIndex::MapKey(key) => match val {
                LhsValue::Map(map) => Ok(Self::MapKey(Some((map, key.as_bytes())))),
                _ => Err(IndexAccessError {
                    index: FieldIndex::MapKey(key.clone()),
                    actual: val.get_type(),
                }),
            },
            FieldIndex::MapEach => match val {
                LhsValue::Array(_) | LhsValue::Map(_) => Ok(Self::MapEach(val.into_iter())),
                _ => Err(IndexAccessError {
                    index: FieldIndex::MapEach,
                    actual: val.get_type(),
                }),
            },
        }
    }
}

impl<'a> Iterator for FieldIndexIterator<'a, '_> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::ArrayIndex(opt) => opt.take().and_then(|(arr, idx)| arr.extract(idx as usize)),
            Self::MapKey(opt) => opt.take().and_then(|(map, key)| map.extract(key)),
            Self::MapEach(iter) => iter.next(),
        }
    }
}

struct MapEachIterator<'a, 'b> {
    indexes: &'b [FieldIndex],
    stack: Vec<FieldIndexIterator<'a, 'b>>,
}

impl<'a, 'b> MapEachIterator<'a, 'b> {
    fn from_indexes(indexes: &'b [FieldIndex]) -> Self {
        Self {
            indexes,
            stack: Vec::with_capacity(indexes.len()),
        }
    }

    fn reset(&mut self, val: LhsValue<'a>) {
        self.stack.clear();
        let first = self.indexes.first().unwrap();
        self.stack
            .push(FieldIndexIterator::new(val, first).unwrap());
    }
}

impl<'a> Iterator for MapEachIterator<'a, '_> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        while !self.stack.is_empty() {
            assert!(self.stack.len() <= self.indexes.len());
            if let Some(nxt) = self.stack.last_mut().unwrap().next() {
                // Check that current iterator is a leaf iterator
                if self.stack.len() == self.indexes.len() {
                    // Return a value if a leaf iterator returned a value
                    return Some(nxt);
                } else {
                    self.stack.push(
                        FieldIndexIterator::new(nxt, &self.indexes[self.stack.len()]).unwrap(),
                    );
                }
            } else {
                // Last iterator is finished, remove it
                self.stack.pop();
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::field_expr::IdentifierExpr;
    use crate::{
        Array, FieldIndex, FilterParser, FunctionArgs, FunctionCallArgExpr, FunctionCallExpr,
        Scheme, SchemeBuilder, SimpleFunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl,
        SimpleFunctionParam,
    };
    use std::sync::LazyLock;

    fn array_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(Array::from_iter([bytes]).into()),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    fn array2_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some({
                let inner = Array::from_iter([bytes]);
                let outer = Array::try_from_iter(Type::Array(Type::Bytes.into()), [inner]).unwrap();
                outer.into()
            }),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    static SCHEME: LazyLock<Scheme> = LazyLock::new(|| {
        let mut builder = SchemeBuilder::new();
        builder
            .add_field("test", Type::Array(Type::Bytes.into()))
            .unwrap();
        builder
            .add_field("test2", Type::Array(Type::Array(Type::Bytes.into()).into()))
            .unwrap();
        builder
            .add_field("map", Type::Map(Type::Bytes.into()))
            .unwrap();
        builder
            .add_function(
                "array",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }]),
                    opt_params: Box::new([]),
                    return_type: Type::Array(Type::Bytes.into()),
                    implementation: SimpleFunctionImpl::new(array_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "array2",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }]),
                    opt_params: Box::new([]),
                    return_type: Type::Array(Type::Array(Type::Bytes.into()).into()),
                    implementation: SimpleFunctionImpl::new(array2_function),
                },
            )
            .unwrap();
        builder.build()
    });

    #[test]
    fn test_array_indices() {
        fn run(i: u32) {
            let filter = format!("test[{i}]");
            assert_ok!(
                FilterParser::new(&SCHEME).lex_as(&filter),
                IndexExpr {
                    identifier: IdentifierExpr::Field(SCHEME.get_field("test").unwrap().to_owned()),
                    indexes: Box::new([FieldIndex::ArrayIndex(i)]),
                }
            );
        }

        run(0);
        run(1);
        run(99);
        run(999);
        run(9999);
        run(99999);

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>("test[-1]"),
            LexErrorKind::ExpectedLiteral("expected positive integer as index"),
            "-1]"
        );
    }

    #[test]
    fn test_map_access() {
        assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"map["a"]"#),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("map").unwrap().to_owned()),
                indexes: Box::new([FieldIndex::MapKey("a".into())]),
            }
        );

        assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"map["😍"]"#),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("map").unwrap().to_owned()),
                indexes: Box::new([FieldIndex::MapKey("😍".into())]),
            }
        );
    }

    #[test]
    fn test_access_with_non_string() {
        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(r#"test[a]"#),
            LexErrorKind::ExpectedLiteral("expected quoted utf8 string or positive integer"),
            "a]"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(r#"map[a]"#),
            LexErrorKind::ExpectedLiteral("expected quoted utf8 string or positive integer"),
            "a]"
        );
    }

    #[test]
    fn test_function_return_selection() {
        let mut ctx = ExecutionContext::new(&SCHEME);
        ctx.set_field_value_from_name("test", Array::from_iter(["value"]))
            .unwrap();
        let array = LhsValue::Array(Array::from_iter(["value"]));
        for (expression, expected) in [
            ("array(test[0])", Ok(array.clone())),
            ("array(test[0])[0]", Ok(LhsValue::from("value"))),
            ("array(test[0])[*]", Ok(array.clone())),
            ("array2(test[0])[0]", Ok(array.clone())),
            ("array2(test[0])[0][*]", Ok(array.clone())),
            ("array2(test[0])[*][0]", Ok(array.clone())),
            ("array2(test[0])[*][*]", Ok(array)),
            ("array2(test[0])[9][*]", Err(Type::array(Type::Bytes))),
            ("array2(test[0])[*][9]", Ok(Array::new(Type::Bytes).into())),
        ] {
            let (index, rest) = FilterParser::new(&SCHEME)
                .lex_as::<IndexExpr>(expression)
                .unwrap();
            assert!(rest.is_empty());
            assert_eq!(index.compile().execute(&ctx), expected, "{expression}");
        }
    }

    #[test]
    fn test_terminal_map_each_preserves_function_result_and_error_types() {
        fn echo<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
            args.next()?.ok()
        }

        let map_type = Type::map(Type::Bytes);
        let mut builder = SchemeBuilder::new();
        for (field, function, ty) in [
            ("map", "echo_map", map_type),
            ("maps", "echo_maps", Type::array(map_type)),
        ] {
            builder.add_optional_field(field, ty).unwrap();
            builder
                .add_function(
                    function,
                    SimpleFunctionDefinition {
                        params: Box::new([SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Field,
                            val_type: ty,
                        }]),
                        opt_params: Box::new([]),
                        return_type: ty,
                        implementation: SimpleFunctionImpl::new(echo),
                    },
                )
                .unwrap();
        }
        let scheme = builder.build();
        let map = Map::try_from_iter::<crate::TypeMismatchError, _>(
            Type::Bytes,
            [Ok((Box::from(b"key".as_slice()), "value"))],
        )
        .unwrap();
        let missing = ExecutionContext::new(&scheme);
        let mut present = ExecutionContext::new(&scheme);
        present
            .set_field_value_from_name("map", map.clone())
            .unwrap();
        present
            .set_field_value_from_name(
                "maps",
                Array::try_from_iter(map_type, [map.clone()]).unwrap(),
            )
            .unwrap();
        for (expression, missing_type) in [
            ("map[*]", Type::array(Type::Bytes)),
            ("echo_map(map)[*]", map_type),
            ("echo_maps(maps)[0][*]", Type::array(Type::Bytes)),
        ] {
            let (index, rest) = FilterParser::new(&scheme)
                .lex_as::<IndexExpr>(expression)
                .unwrap();
            assert!(rest.is_empty());
            let compiled = index.compile();
            assert_eq!(
                compiled.execute(&present),
                Ok(LhsValue::Map(map.clone())),
                "{expression}"
            );
            assert_eq!(
                compiled.execute(&missing),
                Err(missing_type),
                "{expression}"
            );
        }
    }

    #[test]
    fn test_function_call_with_missing_argument_then_index_access() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array(test[0])[0]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array").unwrap().to_owned(),
                    args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: Box::new([FieldIndex::ArrayIndex(0)]),
                    })]),
                    context: None
                }),
                indexes: Box::new([FieldIndex::ArrayIndex(0)]),
            }
        );

        assert_eq!(expr.identifier.get_type(), Type::Array(Type::Bytes.into()));
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(value.execute(&exec_ctx), Err(Type::Bytes));

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array(test[0])[*]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array").unwrap().to_owned(),
                    args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: Box::new([FieldIndex::ArrayIndex(0)]),
                    })]),
                    context: None
                }),
                indexes: Box::new([FieldIndex::MapEach]),
            }
        );

        assert_eq!(expr.identifier.get_type(), Type::Array(Type::Bytes.into()));
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array2(test[0])[*][*]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array2").unwrap().to_owned(),
                    args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: Box::new([FieldIndex::ArrayIndex(0)]),
                    })]),
                    context: None
                }),
                indexes: Box::new([FieldIndex::MapEach, FieldIndex::MapEach]),
            }
        );

        assert_eq!(
            expr.identifier.get_type(),
            Type::Array(Type::Array(Type::Bytes.into()).into())
        );
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array2(test[0])[*][0]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array2").unwrap().to_owned(),
                    args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: Box::new([FieldIndex::ArrayIndex(0)]),
                    })]),
                    context: None
                }),
                indexes: Box::new([FieldIndex::MapEach, FieldIndex::ArrayIndex(0)]),
            }
        );

        assert_eq!(
            expr.identifier.get_type(),
            Type::Array(Type::Array(Type::Bytes.into()).into())
        );
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"array2(test[0])[0][*]"#),
            IndexExpr {
                identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                    function: SCHEME.get_function("array2").unwrap().to_owned(),
                    args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("test").unwrap().to_owned()
                        ),
                        indexes: Box::new([FieldIndex::ArrayIndex(0)]),
                    })]),
                    context: None
                }),
                indexes: Box::new([FieldIndex::ArrayIndex(0), FieldIndex::MapEach]),
            }
        );

        assert_eq!(
            expr.identifier.get_type(),
            Type::Array(Type::Array(Type::Bytes.into()).into())
        );
        assert_eq!(expr.get_type(), Type::Bytes);

        let value = expr.compile();

        let mut exec_ctx = ExecutionContext::new(&SCHEME);

        exec_ctx
            .set_field_value(SCHEME.get_field("test").unwrap(), Array::new(Type::Bytes))
            .unwrap();

        assert_eq!(
            value.execute(&exec_ctx),
            Err(Type::Array(Type::Bytes.into()))
        );
    }

    #[test]
    fn test_mapeach() {
        let filter = "test2[0][*]".to_string();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(&filter),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("test2").unwrap().to_owned()),
                indexes: Box::new([FieldIndex::ArrayIndex(0), FieldIndex::MapEach]),
            }
        );

        assert_eq!(expr.map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Bytes);
        assert_eq!(expr.output_type(), Type::Array(Type::Bytes.into()));

        let filter = "test2[*][0]".to_string();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(&filter),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("test2").unwrap().to_owned()),
                indexes: Box::new([FieldIndex::MapEach, FieldIndex::ArrayIndex(0)]),
            }
        );

        assert_eq!(expr.map_each_count(), 1);
        assert_eq!(expr.get_type(), Type::Bytes);
        assert_eq!(expr.output_type(), Type::Array(Type::Bytes.into()));

        let filter = "test2[*][*]".to_string();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(&filter),
            IndexExpr {
                identifier: IdentifierExpr::Field(SCHEME.get_field("test2").unwrap().to_owned()),
                indexes: Box::new([FieldIndex::MapEach, FieldIndex::MapEach]),
            }
        );

        assert_eq!(expr.map_each_count(), 2);
        assert_eq!(expr.get_type(), Type::Bytes);
        assert_eq!(expr.output_type(), Type::Array(Type::Bytes.into()));

        let filter = "test2[0][*][*]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );

        let filter = "test2[*][0][*]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );

        let filter = "test2[*][*][0]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes
            }),
            "[0]"
        );

        let filter = "test2[*][*][*]".to_string();

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<IndexExpr>(&filter),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes
            }),
            "[*]"
        );
    }

    #[test]
    fn test_flatten() {
        let arr = LhsValue::Array(
            Array::try_from_iter(
                Type::Array(Type::Bytes.into()),
                (0..10).map(|i| Array::from_iter((0..10).map(|j| format!("[{i}][{j}]")))),
            )
            .unwrap(),
        );

        for i in 0..10 {
            let indexes = [FieldIndex::ArrayIndex(i), FieldIndex::MapEach];
            let mut iter = MapEachIterator::from_indexes(&indexes[..]);

            iter.reset(arr.clone());
            for (j, elem) in iter.enumerate() {
                let bytes = match elem {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => unreachable!(),
                };
                assert_eq!(std::str::from_utf8(&bytes).unwrap(), format!("[{i}][{j}]"));
            }

            let indexes = [FieldIndex::MapEach, FieldIndex::ArrayIndex(i)];
            let mut iter = MapEachIterator::from_indexes(&indexes[..]);

            iter.reset(arr.clone());
            for (j, elem) in iter.enumerate() {
                let bytes = match elem {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => unreachable!(),
                };
                assert_eq!(std::str::from_utf8(&bytes).unwrap(), format!("[{j}][{i}]"));
            }
        }

        let indexes = [FieldIndex::MapEach, FieldIndex::MapEach];
        let mut iter = MapEachIterator::from_indexes(&indexes[..]);
        let mut i = 0;
        let mut j = 0;

        iter.reset(arr.clone());
        for elem in iter {
            let bytes = match elem {
                LhsValue::Bytes(bytes) => bytes,
                _ => unreachable!(),
            };
            assert_eq!(std::str::from_utf8(&bytes).unwrap(), format!("[{i}][{j}]"));
            j = (j + 1) % 10;
            i += (j == 0) as u32;
        }
    }
    #[test]
    fn test_native_custom_comparators_can_consume_collections() {
        use crate::{DefaultCompiler, EvaluationContext, HasScheme, ListMatcher, ListRef};
        use std::collections::BTreeMap;

        struct Request {
            scheme: Scheme,
            rows: Vec<Vec<Vec<String>>>,
            maps: Vec<BTreeMap<Box<[u8]>, String>>,
        }
        impl HasScheme for Request {
            fn scheme(&self) -> &Scheme {
                &self.scheme
            }
        }
        impl EvaluationContext for Request {
            type UserData = ();

            fn get_user_data(&self) -> &() {
                &()
            }

            fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
                unreachable!()
            }
        }
        crate::wirefilter_fields! {
            impl NativeFields for Request {
                "rows" => {
                    fn(request: &Request) -> &Vec<Vec<Vec<String>>> {
                        &request.rows
                    }
                },
                "maps" => {
                    fn(request: &Request) -> &Vec<BTreeMap<Box<[u8]>, String>> {
                        &request.maps
                    }
                },
            }
        }
        struct Nonempty;
        impl<F: ContextFamily<UserData = ()>> Compare<(), F> for Nonempty {
            fn compare<'ctx, 'data: 'ctx>(
                &self,
                value: &LhsValue<'ctx>,
                _: &'ctx F::Context<'data>,
            ) -> bool {
                match value {
                    LhsValue::Array(values) => !values.is_empty(),
                    LhsValue::Map(values) => !values.is_empty(),
                    _ => panic!("custom comparator requires a complete collection"),
                }
            }
        }
        let scheme = crate::Scheme! {
            rows: Array(Array(Array(Bytes))),
            maps: Array(Map(Bytes)),
        }
        .build();
        let native = Request {
            scheme: scheme.clone(),
            rows: vec![vec![vec![], vec!["value".into()]], vec![]],
            maps: vec![
                BTreeMap::new(),
                BTreeMap::from([(b"key".as_slice().into(), "value".into())]),
            ],
        };
        NativeFields::validate_scheme(&scheme).unwrap();
        let mut stored = ExecutionContext::new(&scheme);
        stored
            .set_field_value(scheme.get_field("rows").unwrap(), (&native.rows).into_lhs())
            .unwrap();
        stored
            .set_field_value(scheme.get_field("maps").unwrap(), (&native.maps).into_lhs())
            .unwrap();
        for (name, indexes) in [
            ("rows", vec![]),
            ("rows", vec![FieldIndex::ArrayIndex(8)]),
            ("rows", vec![FieldIndex::MapEach]),
            ("rows", vec![FieldIndex::MapEach, FieldIndex::MapEach]),
            ("maps", vec![FieldIndex::MapEach]),
        ] {
            for missing in [false, true] {
                let index = IndexExpr {
                    identifier: IdentifierExpr::Field(scheme.get_field(name).unwrap().to_owned()),
                    indexes: indexes.clone().into_boxed_slice(),
                };
                let expected = index.clone().compile_with(
                    &mut DefaultCompiler::<()>::new(),
                    missing,
                    Nonempty,
                );
                let actual = index.compile_with(
                    &mut DefaultCompiler::<(), NativeFields>::new(),
                    missing,
                    Nonempty,
                );
                match (expected, actual) {
                    (CompiledExpr::One(expected), CompiledExpr::One(actual)) => {
                        assert_eq!(expected.execute(&stored), actual.execute(&native));
                    }
                    (CompiledExpr::Vec(expected), CompiledExpr::Vec(actual)) => {
                        assert_eq!(expected.execute(&stored), actual.execute(&native));
                    }
                    _ => panic!("comparison cardinality changed"),
                }
            }
        }
    }

    #[test]
    fn test_native_indexed_value_expressions_match_stored_values() {
        use crate::{DefaultCompiler, EvaluationContext, HasScheme, ListMatcher, ListRef};
        use std::collections::BTreeMap;

        type Rows = BTreeMap<Box<[u8]>, Vec<Vec<Box<str>>>>;
        type Groups = Vec<BTreeMap<Box<[u8]>, Vec<Box<str>>>>;
        struct Request {
            scheme: Scheme,
            rows: Option<Rows>,
            groups: Option<Groups>,
        }
        impl HasScheme for Request {
            fn scheme(&self) -> &Scheme {
                &self.scheme
            }
        }
        impl EvaluationContext for Request {
            type UserData = ();

            fn get_user_data(&self) -> &() {
                &()
            }

            fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
                unreachable!()
            }
        }
        crate::wirefilter_fields! {
            impl NativeFields for Request {
                "rows" => {
                    fn(request: &Request) -> Option<&Rows> {
                        request.rows.as_ref()
                    }
                },
                "groups" => {
                    fn(request: &Request) -> Option<&Groups> {
                        request.groups.as_ref()
                    }
                },
            }
        }
        let mut builder = SchemeBuilder::new();
        builder
            .add_optional_field("rows", Type::map(Type::array(Type::array(Type::Bytes))))
            .unwrap();
        builder
            .add_optional_field("groups", Type::array(Type::map(Type::array(Type::Bytes))))
            .unwrap();
        let scheme = builder.build();
        NativeFields::validate_scheme(&scheme).unwrap();

        for present in [true, false] {
            let native = Request {
                scheme: scheme.clone(),
                rows: present.then(|| {
                    BTreeMap::from([
                        (Box::from(b"z".as_slice()), vec![vec!["z0".into()]]),
                        (
                            Box::from(b"selected".as_slice()),
                            vec![vec!["s0".into(), "s1".into()], vec![], vec!["s2".into()]],
                        ),
                        (Box::from(b"empty".as_slice()), vec![]),
                        (Box::from(b"a".as_slice()), vec![vec!["a0".into()]]),
                    ])
                }),
                groups: present.then(|| {
                    vec![
                        BTreeMap::from([
                            (Box::from(b"z".as_slice()), vec!["z1".into()]),
                            (
                                Box::from(b"values".as_slice()),
                                vec!["v0".into(), "v1".into()],
                            ),
                            (Box::from(b"empty".as_slice()), vec![]),
                            (Box::from(b"a".as_slice()), vec!["a1".into()]),
                        ]),
                        BTreeMap::new(),
                        BTreeMap::from([(Box::from(b"values".as_slice()), vec!["v2".into()])]),
                    ]
                }),
            };
            let mut stored = ExecutionContext::new(&scheme);
            if let Some(rows) = &native.rows {
                stored
                    .set_field_value_from_name("rows", rows.into_lhs())
                    .unwrap();
            }
            if let Some(groups) = &native.groups {
                stored
                    .set_field_value_from_name("groups", groups.into_lhs())
                    .unwrap();
            }

            for expression in [
                "rows",
                r#"rows["selected"]"#,
                r#"rows["selected"][0]"#,
                r#"rows["selected"][0][1]"#,
                r#"rows["selected"][0][*]"#,
                r#"rows["selected"][*]"#,
                r#"rows["selected"][*][*]"#,
                r#"rows["selected"][*][0]"#,
                r#"rows["selected"][*][9]"#,
                r#"rows["selected"][9]"#,
                r#"rows["selected"][9][*]"#,
                r#"rows["selected"][9][0]"#,
                r#"rows["empty"][*]"#,
                r#"rows["empty"][*][*]"#,
                r#"rows["empty"][*][0]"#,
                r#"rows["missing"]"#,
                r#"rows["missing"][*]"#,
                r#"rows["missing"][0][*]"#,
                r#"rows["missing"][*][*]"#,
                r#"rows["missing"][*][0]"#,
                "rows[*]",
                "rows[*][*]",
                "rows[*][*][*]",
                "rows[*][0][*]",
                "groups",
                "groups[0]",
                "groups[0][*]",
                "groups[0][*][*]",
                "groups[0][*][0]",
                r#"groups[0]["values"][*]"#,
                r#"groups[0]["values"][1]"#,
                r#"groups[0]["missing"][*]"#,
                "groups[1][*]",
                "groups[1][*][*]",
                "groups[9][*]",
                "groups[9][*][*]",
                "groups[9][*][0]",
                r#"groups[9]["values"][*]"#,
                r#"groups[*]["values"][*]"#,
                r#"groups[*]["values"][0]"#,
                r#"groups[*]["missing"][*]"#,
                "groups[*][*][*]",
            ] {
                let (index, rest) = FilterParser::new(&scheme)
                    .lex_as::<IndexExpr>(expression)
                    .unwrap();
                assert!(rest.is_empty(), "{expression}");
                let expected = index
                    .clone()
                    .compile_with_compiler(&mut DefaultCompiler::<()>::new());
                let actual =
                    index.compile_with_compiler(&mut DefaultCompiler::<(), NativeFields>::new());
                let expected = expected.execute(&stored);
                let actual = actual.execute(&native);
                assert_eq!(actual, expected, "{expression}, present={present}");
                if !present {
                    assert!(actual.is_err(), "{expression}");
                    continue;
                }

                // Check flattening order and the difference between a missing
                // selection before `[*]` and a missing optional root.
                let flat: Option<&[&str]> = match expression {
                    r#"rows["selected"][*][*]"# => Some(&["s0", "s1", "s2"]),
                    r#"rows["selected"][*][0]"# => Some(&["s0", "s2"]),
                    "rows[*][*][*]" => Some(&["a0", "s0", "s1", "s2", "z0"]),
                    "rows[*][0][*]" => Some(&["a0", "s0", "s1", "z0"]),
                    "groups[0][*][*]" => Some(&["a1", "v0", "v1", "z1"]),
                    "groups[0][*][0]" => Some(&["a1", "v0", "z1"]),
                    r#"groups[*]["values"][*]"# => Some(&["v0", "v1", "v2"]),
                    r#"groups[*]["values"][0]"# => Some(&["v0", "v2"]),
                    "groups[*][*][*]" => Some(&["a1", "v0", "v1", "z1", "v2"]),
                    r#"rows["selected"][*][9]"#
                    | r#"rows["empty"][*][*]"#
                    | r#"rows["empty"][*][0]"#
                    | r#"rows["missing"][*][*]"#
                    | r#"rows["missing"][*][0]"#
                    | "groups[1][*][*]"
                    | "groups[9][*][*]"
                    | "groups[9][*][0]"
                    | r#"groups[*]["missing"][*]"# => Some(&[]),
                    _ => None,
                };
                if let Some(values) = flat {
                    assert_eq!(
                        actual.as_ref().unwrap(),
                        &LhsValue::Array(Array::from_iter(values.iter().copied())),
                        "{expression}",
                    );
                }
                if expression == "groups[0][*]" {
                    // A single terminal `map[*]` retains its map for the
                    // mapped function, whose iteration follows byte-key order.
                    let LhsValue::Map(map) = actual.unwrap() else {
                        panic!("terminal map[*] must retain the map");
                    };
                    let values: Vec<_> = map.into_values().collect();
                    assert_eq!(
                        values,
                        vec![
                            LhsValue::Array(Array::from_iter(["a1"])),
                            LhsValue::Array(Array::new(Type::Bytes)),
                            LhsValue::Array(Array::from_iter(["v0", "v1"])),
                            LhsValue::Array(Array::from_iter(["z1"])),
                        ],
                    );
                }
            }
        }
    }
}
