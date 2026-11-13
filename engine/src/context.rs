//! Runtime contexts and statically bound field access.
//!
//! A context family associates compiled expressions with a context that may borrow
//! request data. Field binding happens during filter compilation; evaluation calls
//! the concrete getter captured by the compiled expression.

use crate::native::values::{IntoLhsValue, NativeValue, ValueType};
use crate::{ExecutionContext, Field, LhsValue, List, ListMatcher, ListRef, Scheme, Type};
use std::marker::PhantomData;

/// The scheme associated with a runtime context.
pub trait HasScheme {
    /// Scheme used to interpret fields and lists.
    fn scheme(&self) -> &Scheme;
}

/// State shared by expression evaluation, independently of field storage.
///
/// Together with [`HasScheme`], this trait exposes the scheme, list matchers,
/// and user data available during evaluation. Field getters are bound separately
/// through [`ContextFamily`].
///
/// An application context can use its existing storage or forward these methods
/// to a borrowed [`crate::NativeContextState`]. [`ExecutionContext`] already implements
/// this interface alongside its stored field values. See [`crate::native`] for
/// a complete example using native fields and reusable state.
pub trait EvaluationContext: HasScheme {
    /// Per-evaluation state used by compiler customizations.
    type UserData;

    /// State retained by the embedding runtime.
    fn get_user_data(&self) -> &Self::UserData;

    /// Matcher for a list registered in this context's scheme.
    fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher;

    /// Matcher for the list registered for a Wirefilter type, if present.
    #[inline]
    fn get_list_matcher_from_type(&self, ty: &Type) -> Option<&dyn ListMatcher> {
        let list = self.scheme().get_list(ty)?;
        Some(self.get_list_matcher(list))
    }

    /// Matcher access after the outer filter has checked scheme compatibility.
    #[inline]
    fn get_list_matcher_unchecked(&self, list: &List) -> &dyn ListMatcher {
        self.get_list_matcher(list.as_ref())
    }
}

/// Mutable executor state, independently of native request field storage.
///
/// Extends [`EvaluationContext`] for updating list matchers and user data. Native
/// filter evaluation only requires the shared interface; an application adds this
/// trait when it also needs mutable access. Both [`ExecutionContext`] and
/// [`crate::NativeContextState`] implement it.
pub trait EvaluationContextMut: EvaluationContext {
    /// State used to initialize and clean up compiler customizations.
    fn get_user_data_mut(&mut self) -> &mut Self::UserData;

    /// Mutable matcher for a list registered in this context's scheme.
    fn get_list_matcher_mut(&mut self, list: ListRef<'_>) -> &mut dyn ListMatcher;

    /// Mutable matcher for the list registered for a Wirefilter type, if present.
    #[inline]
    fn get_list_matcher_mut_from_type(&mut self, ty: &Type) -> Option<&mut dyn ListMatcher> {
        let list = self.scheme().get_list(ty)?.to_owned();
        Some(self.get_list_matcher_mut(list.as_ref()))
    }
}

/// A field-definition problem detected before filters are evaluated.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FieldDefinitionError {
    /// A scheme field has no getter.
    #[error("Missing native field getter for {0}")]
    MissingGetter(Box<str>),
    /// A getter names a field absent from the scheme.
    #[error("Unknown native field {0}")]
    UnknownField(Box<str>),
    /// More than one getter names the same field.
    #[error("Duplicate native field getter for {0}")]
    DuplicateGetter(Box<str>),
    /// A getter for a mandatory scheme field can return no value.
    #[error("Native field {0} is mandatory but its getter returns Option")]
    OptionalGetterForMandatoryField(Box<str>),
    /// Getter and scheme types differ.
    #[error("Native field {name} has type {getter_type}, expected {scheme_type}")]
    TypeMismatch {
        /// Field name.
        name: Box<str>,
        /// Type declared in the scheme.
        scheme_type: Type,
        /// Type returned by the getter.
        getter_type: Type,
    },
}

/// All field-definition problems found during explicit scheme validation.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("Invalid native field definitions: {0:?}")]
pub struct SchemeValidationError(pub Box<[FieldDefinitionError]>);

/// A failure to bind a field or prepare its native access during compilation.
///
/// Binding APIs return this error. The infallible expression compilation APIs
/// panic on a binding failure; filter execution does not return this error.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FieldBindingError {
    /// A field cannot be resolved by the native context family.
    #[error("Unknown native field {0}")]
    UnknownField(Box<str>),
    /// The getter's logical type differs from the scheme.
    #[error("Native field {field} has type {actual}, expected {expected}")]
    TypeMismatch {
        /// Field whose type differs.
        field: Box<str>,
        /// Type declared in the scheme.
        expected: Type,
        /// Type provided by the getter.
        actual: Type,
    },
    /// A path is incompatible with the declared native type.
    ///
    /// Produced during path compilation, not evaluation. Parsed paths for
    /// matching scheme and native types are expected to be compatible.
    #[error("Unsupported native value operation: {0}")]
    Unsupported(&'static str),
}

/// A lifetime-independent description of contexts and their field bindings.
///
/// A separate marker can associate `Context<'data>` with a borrowing request
/// context while compiled filters retain no request lifetime. An owned context
/// type satisfying `'static` may instead implement this trait itself and use
/// `type Context<'data> = Self`. The family is used as a type parameter; compiled
/// expressions do not store an instance of it. [`crate::wirefilter_fields!`]
/// generates a separate marker for both forms of context.
///
/// [`EvaluationContext`] describes the state available during evaluation; this
/// trait selects that context type and binds its field getters during compilation.
/// It does not own the context, request data, or [`crate::NativeContextState`]. See
/// [`crate::native`] for a complete example showing their relationship.
pub trait ContextFamily: Sized + 'static {
    /// State exposed to compiler customizations.
    type UserData: 'static;

    /// The runtime context, possibly retaining request references.
    type Context<'data>: EvaluationContext<UserData = Self::UserData>;

    /// Resolve a field and pass its concrete getter to the compilation operation.
    /// Ownership of the logical field transfers to the consumer or stored getter.
    fn bind<B: FieldConsumer<Self>>(
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError>;

    /// Validate field coverage, types, and required presence without evaluating getters.
    ///
    /// Applications must call this explicitly during initialization for each
    /// scheme and native context family, before loading rulesets or compiling
    /// expressions. A failed check is an initialization error. Parsing,
    /// compilation, and evaluation do not invoke this method automatically.
    ///
    /// Stored contexts obtain their field table directly from the scheme and need
    /// no additional validation. Native families override this method.
    fn validate_scheme(_: &Scheme) -> Result<(), SchemeValidationError> {
        Ok(())
    }
}

/// A context reference whose type records that request data outlives this access.
///
/// Higher-ranked closures over an arbitrary context family's associated type do
/// not otherwise imply this lifetime relationship. The witness lets compiled
/// value expressions return borrowed payloads, including from invariant contexts.
/// It contains only the original reference and requires no allocation.
#[repr(transparent)]
pub struct ContextRef<'ctx, 'data, F: ContextFamily> {
    context: &'ctx F::Context<'data>,
    lifetime: PhantomData<&'ctx &'data ()>,
}

impl<F: ContextFamily> Copy for ContextRef<'_, '_, F> {}

impl<F: ContextFamily> Clone for ContextRef<'_, '_, F> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<'ctx, 'data: 'ctx, F: ContextFamily> ContextRef<'ctx, 'data, F> {
    /// Record the relationship between the context borrow and its retained data.
    #[inline]
    pub fn new(context: &'ctx F::Context<'data>) -> Self {
        Self {
            context,
            lifetime: PhantomData,
        }
    }

    /// Return the original context borrow, independently of the witness's storage.
    #[inline]
    pub fn context(self) -> &'ctx F::Context<'data> {
        self.context
    }
}

/// An operation that composes field access with expression compilation.
pub trait FieldConsumer<F: ContextFamily>: Sized {
    /// Executable expression produced by this operation.
    type Output;

    /// Compile using a native getter whose concrete type remains known.
    /// `field` is the original logical field supplied to the binding operation.
    fn native<G: FieldGetter<F>>(
        self,
        field: Field,
        getter: G,
    ) -> Result<Self::Output, FieldBindingError>;

    /// Compile using an existing stored value without rebuilding it on access.
    fn stored<G: StoredFieldGetter<F>>(self, getter: G) -> Result<Self::Output, FieldBindingError>;
}

/// A native field's representation across request and access lifetimes.
pub trait ProviderFamily: 'static {
    /// Recursive Wirefilter type represented by the provider.
    type ValueType: ValueType;

    /// Storage usable by generated contexts and custom adapters.
    type Storage<'data>;

    /// A reference or selection descriptor returned by one field access.
    type Value<'ctx, 'data>: NativeValue<ValueType = Self::ValueType> + IntoLhsValue<'ctx>
    where
        'data: 'ctx;

    /// Obtain a shorter access to retained storage.
    fn reborrow<'ctx, 'data: 'ctx>(value: &'ctx Self::Storage<'data>) -> Self::Value<'ctx, 'data>;
}

/// A provider borrowing native storage whose Rust type has no request lifetime.
pub struct BorrowedValueProvider<T: ?Sized>(PhantomData<fn() -> T>);

impl<T: NativeValue + ?Sized + 'static> ProviderFamily for BorrowedValueProvider<T> {
    type Storage<'data> = &'data T;
    type Value<'ctx, 'data>
        = &'ctx T
    where
        'data: 'ctx;
    type ValueType = T::ValueType;

    #[inline]
    fn reborrow<'ctx, 'data: 'ctx>(value: &'ctx Self::Storage<'data>) -> Self::Value<'ctx, 'data> {
        value
    }
}

/// A provider returning a value whose Rust type has no request lifetime.
///
/// Scalar getters can return values directly. Custom by-value descriptors that
/// borrow request data instead implement [`ProviderFamily`] with those lifetimes.
pub struct OwnedValueProvider<T>(PhantomData<fn() -> T>);

impl<T> ProviderFamily for OwnedValueProvider<T>
where
    T: NativeValue + Clone + 'static,
    for<'a> T: IntoLhsValue<'a>,
{
    type Storage<'data> = T;
    type Value<'ctx, 'data>
        = T
    where
        'data: 'ctx;
    type ValueType = T::ValueType;

    #[inline]
    fn reborrow<'ctx, 'data: 'ctx>(value: &'ctx Self::Storage<'data>) -> Self::Value<'ctx, 'data> {
        value.clone()
    }
}

/// Concrete field access captured inside an executable expression.
pub trait FieldGetter<F: ContextFamily>: Send + Sync + 'static {
    /// The native field representation.
    type Provider: ProviderFamily;

    /// Read the field for this evaluation without constructing a value enum.
    ///
    /// `field` is the original logical field supplied to the binding operation,
    /// including its scheme index, name, type, and optionality. Its borrow is
    /// independent of the context borrow and cannot be retained in the result.
    ///
    /// A getter bound to a mandatory scheme field must return `Some`. The field
    /// macro enforces this through its return signatures and explicit scheme
    /// validation; handwritten implementations must uphold the same contract.
    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx F::Context<'data>,
        field: &Field,
    ) -> Option<<Self::Provider as ProviderFamily>::Value<'ctx, 'data>>;
}

/// A getter result preserving the relationship between access and request lifetimes.
///
/// This transparent wrapper keeps the provider's associated value outside the
/// higher-ranked function pointer's return projection. The value has exactly
/// the representation of `Option<P::Value<'ctx, 'data>>`.
// Returning the projection directly encounters rustc's higher-ranked lifetime
// limitation (rust-lang/rust#100013), despite ContextRef carrying the constraint.
#[repr(transparent)]
pub struct OptionalFieldGetterResult<'ctx, 'data: 'ctx, P: ProviderFamily> {
    value: Option<P::Value<'ctx, 'data>>,
}

impl<'ctx, 'data: 'ctx, P: ProviderFamily> OptionalFieldGetterResult<'ctx, 'data, P> {
    /// Retain the result of a getter for the context access lifetime.
    pub fn new(value: Option<P::Value<'ctx, 'data>>) -> Self {
        Self { value }
    }
}

/// Field access represented by a typed function pointer.
///
/// Fields in the same context family using the same provider share this getter
/// type, allowing consumers to share their compiled expression implementations.
/// The pointer selects the field's getter on each access; native values retain
/// their concrete type and do not require an intermediate value enum or allocation.
/// Handwritten getters retaining additional state can implement [`FieldGetter`]
/// directly instead.
pub struct FieldGetterFn<F: ContextFamily, P: ProviderFamily> {
    callback: for<'ctx, 'data, 'field> fn(
        ContextRef<'ctx, 'data, F>,
        &'field Field,
    ) -> OptionalFieldGetterResult<'ctx, 'data, P>,
}

impl<F: ContextFamily, P: ProviderFamily> FieldGetterFn<F, P> {
    /// Wrap a getter without allocating or retaining a request lifetime.
    ///
    /// The context witness records that request data outlives the access. Field
    /// metadata is borrowed independently and cannot be retained in the result.
    /// A mandatory field's result must contain `Some`, as for [`FieldGetter`].
    pub fn new(
        callback: for<'ctx, 'data, 'field> fn(
            ContextRef<'ctx, 'data, F>,
            &'field Field,
        ) -> OptionalFieldGetterResult<'ctx, 'data, P>,
    ) -> Self {
        Self { callback }
    }
}

impl<F: ContextFamily, P: ProviderFamily> FieldGetter<F> for FieldGetterFn<F, P> {
    type Provider = P;

    // Keep this adapter as thin as the macro's concrete FieldGetter adapter.
    #[inline]
    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx F::Context<'data>,
        field: &Field,
    ) -> Option<P::Value<'ctx, 'data>> {
        (self.callback)(ContextRef::new(context), field).value
    }
}

/// A plain getter result preserving access and request lifetime relationships.
///
/// Like [`OptionalFieldGetterResult`], this transparent wrapper avoids a higher-ranked
/// associated-type projection in the callback signature. It contains a plain
/// native value; presence is added by [`RequiredFieldGetterFn::get`] after the
/// function pointer returns.
#[repr(transparent)]
pub struct RequiredFieldGetterResult<'ctx, 'data: 'ctx, P: ProviderFamily> {
    value: P::Value<'ctx, 'data>,
}

impl<'ctx, 'data: 'ctx, P: ProviderFamily> RequiredFieldGetterResult<'ctx, 'data, P> {
    /// Retain an always-present value for the context access lifetime.
    pub fn new(value: P::Value<'ctx, 'data>) -> Self {
        Self { value }
    }
}

/// Always-present field access represented by a typed function pointer.
///
/// Plain-return getters in the same context family using the same provider share
/// this getter type. The callback returns a plain native value; this wrapper
/// constructs `Some` after calling it, so consumers can establish presence
/// independently of the selected callback. The scheme field may be mandatory or
/// optional. Getters returning `Option` use [`FieldGetterFn`] instead.
pub struct RequiredFieldGetterFn<F: ContextFamily, P: ProviderFamily> {
    callback: for<'ctx, 'data, 'field> fn(
        ContextRef<'ctx, 'data, F>,
        &'field Field,
    ) -> RequiredFieldGetterResult<'ctx, 'data, P>,
}

impl<F: ContextFamily, P: ProviderFamily> RequiredFieldGetterFn<F, P> {
    /// Wrap a plain-return getter without allocation or a retained request lifetime.
    ///
    /// Field metadata is borrowed independently and cannot be retained in the
    /// result. The callback must produce a native value on every access.
    pub fn new(
        callback: for<'ctx, 'data, 'field> fn(
            ContextRef<'ctx, 'data, F>,
            &'field Field,
        ) -> RequiredFieldGetterResult<'ctx, 'data, P>,
    ) -> Self {
        Self { callback }
    }
}

impl<F: ContextFamily, P: ProviderFamily> FieldGetter<F> for RequiredFieldGetterFn<F, P> {
    type Provider = P;

    // Match the optional wrapper's thin adapter while making presence visible
    // to consumers without inspecting the callback implementation.
    #[inline]
    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx F::Context<'data>,
        field: &Field,
    ) -> Option<P::Value<'ctx, 'data>> {
        Some((self.callback)(ContextRef::new(context), field).value)
    }
}

/// Concrete access to an existing stored Wirefilter value.
pub trait StoredFieldGetter<F: ContextFamily>: Send + Sync + 'static {
    /// The original logical field supplied to the binding operation.
    ///
    /// Its name, type, and optionality apply to the expression even if this
    /// getter reads another storage location. Consumers borrow this metadata
    /// rather than retaining another owned copy of the field.
    fn field(&self) -> &Field;

    /// Borrow a value already retained by the runtime context.
    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx F::Context<'data>,
    ) -> Option<&'ctx LhsValue<'ctx>>;
}

/// Compatibility family for the ordinary field-table execution context.
pub struct StoredContextFamily<U = ()>(PhantomData<fn() -> U>);

impl<U: 'static> ContextFamily for StoredContextFamily<U> {
    type Context<'data> = ExecutionContext<'data, U>;
    type UserData = U;

    #[inline]
    fn bind<B: FieldConsumer<Self>>(
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError> {
        consumer.stored(StoredGetter::<U>(field, PhantomData))
    }
}

struct StoredGetter<U>(Field, PhantomData<fn() -> U>);

impl<U: 'static> StoredFieldGetter<StoredContextFamily<U>> for StoredGetter<U> {
    #[inline]
    fn field(&self) -> &Field {
        &self.0
    }

    #[inline]
    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx ExecutionContext<'data, U>,
    ) -> Option<&'ctx LhsValue<'ctx>> {
        context.get_field_value_unchecked(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ContextFamily, FieldBindingError, FieldConsumer, SchemeValidationError, StoredFieldGetter,
    };
    use crate::{ExecutionContext, Field, Scheme};

    #[test]
    fn test_schema_validation_is_explicit() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static VALIDATIONS: AtomicUsize = AtomicUsize::new(0);
        struct Family;
        struct Getter(Field);
        impl ContextFamily for Family {
            type Context<'data> = ExecutionContext<'data>;
            type UserData = ();

            fn bind<B: FieldConsumer<Self>>(
                field: Field,
                consumer: B,
            ) -> Result<B::Output, FieldBindingError> {
                consumer.stored(Getter(field))
            }

            fn validate_scheme(scheme: &Scheme) -> Result<(), SchemeValidationError> {
                VALIDATIONS.fetch_add(1, Ordering::Relaxed);
                crate::validate_field_definitions(scheme, &[("flag", crate::Type::Bool, false)])
            }
        }
        impl StoredFieldGetter<Family> for Getter {
            fn field(&self) -> &Field {
                &self.0
            }

            fn get<'ctx, 'data: 'ctx>(
                &self,
                context: &'ctx ExecutionContext<'data>,
            ) -> Option<&'ctx crate::LhsValue<'ctx>> {
                context.get_field_value_unchecked(&self.0)
            }
        }

        let scheme = Scheme! { flag: Bool }.build();
        Family::validate_scheme(&scheme).unwrap();
        assert_eq!(VALIDATIONS.load(Ordering::Relaxed), 1);

        let mut compiler = crate::DefaultCompiler::<(), Family>::new();
        let mut context = ExecutionContext::new(&scheme);
        context.set_field_value_from_name("flag", true).unwrap();
        for _ in 0..3 {
            let filter = scheme
                .parse("flag")
                .unwrap()
                .compile_with_compiler(&mut compiler);
            let value = scheme
                .parse_value("flag")
                .unwrap()
                .compile_with_compiler(&mut compiler);
            assert!(filter.execute(&context).unwrap());
            assert_eq!(
                value.execute(&context).unwrap(),
                Ok(crate::LhsValue::Bool(true))
            );
        }
        assert_eq!(VALIDATIONS.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_custom_stored_getter_uses_logical_field_metadata() {
        struct Family;
        struct Getter(Field);
        impl ContextFamily for Family {
            type Context<'data> = ExecutionContext<'data>;
            type UserData = ();

            fn bind<B: FieldConsumer<Self>>(
                field: Field,
                consumer: B,
            ) -> Result<B::Output, FieldBindingError> {
                consumer.stored(Getter(field))
            }
        }
        impl StoredFieldGetter<Family> for Getter {
            fn field(&self) -> &Field {
                &self.0
            }

            fn get<'ctx, 'data: 'ctx>(
                &self,
                context: &'ctx ExecutionContext<'data>,
            ) -> Option<&'ctx crate::LhsValue<'ctx>> {
                // Both logical fields read the same optional storage slot.
                let storage = context.scheme().get_field("storage").unwrap();
                context.get_field_value(storage)
            }
        }
        #[derive(Default)]
        struct Compiler {
            bindings: usize,
        }
        impl crate::Compiler for Compiler {
            type Family = Family;
            type U = ();

            fn bind_field<B: FieldConsumer<Self::Family>>(
                &mut self,
                field: Field,
                consumer: B,
            ) -> Result<B::Output, FieldBindingError> {
                self.bindings += 1;
                Family::bind(field, consumer)
            }
        }

        let mut builder = crate::SchemeBuilder::new();
        builder.add_field("required", crate::Type::Bool).unwrap();
        builder
            .add_optional_field("optional", crate::Type::Bool)
            .unwrap();
        builder
            .add_optional_field("storage", crate::Type::Bool)
            .unwrap();
        let scheme = builder.build();
        let mut compiler = Compiler::default();
        let required = scheme
            .parse("required")
            .unwrap()
            .compile_with_compiler(&mut compiler);
        let optional = scheme
            .parse("optional")
            .unwrap()
            .compile_with_compiler(&mut compiler);
        let required_value = scheme
            .parse_value("required")
            .unwrap()
            .compile_with_compiler(&mut compiler);
        let optional_value = scheme
            .parse_value("optional")
            .unwrap()
            .compile_with_compiler(&mut compiler);
        assert_eq!(compiler.bindings, 4);

        let mut context = ExecutionContext::new(&scheme);
        assert!(!optional.execute(&context).unwrap());
        assert_eq!(
            optional_value.execute(&context).unwrap(),
            Err(crate::Type::Bool)
        );
        let operations: [&dyn Fn(); 2] = [
            &|| {
                let _ = required.execute(&context);
            },
            &|| {
                let _ = required_value.execute(&context);
            },
        ];
        for operation in operations {
            let panic =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(operation)).unwrap_err();
            assert_eq!(
                panic.downcast_ref::<String>().map(String::as_str),
                Some("Field required was registered as mandatory but not given a value"),
            );
        }
        for value in [false, true] {
            context.set_field_value_from_name("storage", value).unwrap();
            assert_eq!(required.execute(&context).unwrap(), value);
            assert_eq!(optional.execute(&context).unwrap(), value);
            assert_eq!(
                required_value.execute(&context).unwrap(),
                Ok(crate::LhsValue::Bool(value))
            );
            assert_eq!(
                optional_value.execute(&context).unwrap(),
                Ok(crate::LhsValue::Bool(value))
            );
        }
        assert_eq!(compiler.bindings, 4);
    }

    type Headers = std::collections::BTreeMap<Box<[u8]>, Vec<Box<str>>>;

    struct NativeContext {
        scheme: Scheme,
        names: Vec<Box<str>>,
        flags: Vec<bool>,
        other_flags: Vec<bool>,
        text: Option<Box<str>>,
        other_text: Option<Box<str>>,
        num: Option<i64>,
        other_num: Option<i64>,
        ip: std::net::IpAddr,
        headers: Headers,
        required: Option<Box<str>>,
        lists: Box<[Box<dyn crate::ListMatcher>]>,
        list_accesses: std::cell::Cell<usize>,
    }

    impl super::HasScheme for NativeContext {
        fn scheme(&self) -> &Scheme {
            &self.scheme
        }
    }

    impl super::EvaluationContext for NativeContext {
        type UserData = ();

        fn get_user_data(&self) -> &() {
            &()
        }

        fn get_list_matcher(&self, list: crate::ListRef<'_>) -> &dyn crate::ListMatcher {
            self.list_accesses.set(self.list_accesses.get() + 1);
            &*self.lists[list.index()]
        }
    }

    crate::wirefilter_fields! {
        impl NativeFields for NativeContext {
            "names" => {
                fn(ctx: &NativeContext) -> &Vec<Box<str>> { &ctx.names }
            },
            "flags" => {
                fn(ctx: &NativeContext) -> &Vec<bool> { &ctx.flags }
            },
            "other_flags" => {
                fn(ctx: &NativeContext) -> &Vec<bool> { &ctx.other_flags }
            },
            "text" => {
                fn(ctx: &NativeContext) -> Option<&str> { ctx.text.as_deref() }
            },
            "other_text" => {
                fn(ctx: &NativeContext) -> Option<&str> { ctx.other_text.as_deref() }
            },
            "num" => {
                fn(ctx: &NativeContext) -> Option<i64> { ctx.num }
            },
            "other_num" => {
                fn(ctx: &NativeContext) -> Option<i64> { ctx.other_num }
            },
            "ip" => {
                fn(ctx: &NativeContext) -> std::net::IpAddr { ctx.ip }
            },
            "headers" => {
                fn(ctx: &NativeContext) -> &Headers { &ctx.headers }
            },
            "required" => {
                fn(ctx: &NativeContext) -> &str {
                    ctx.required.as_deref().expect("test context has its required field")
                }
            },
        }
    }

    fn echo<'a>(args: crate::FunctionArgs<'_, 'a>) -> Option<crate::LhsValue<'a>> {
        args.next()?.ok()
    }

    fn owned_names<'a>(args: crate::FunctionArgs<'_, 'a>) -> Option<crate::LhsValue<'a>> {
        args.next()?.as_ref().ok()?;
        Some(crate::LhsValue::Array(
            crate::Array::try_from_iter(
                crate::Type::Bytes,
                ["Accept", "Other"].map(|s| crate::LhsValue::from(Box::<str>::from(s))),
            )
            .unwrap(),
        ))
    }

    fn native_context(nil_not_equal: bool) -> NativeContext {
        use crate::{
            SimpleFunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl,
            SimpleFunctionParam, Type,
        };
        let array_bytes = Type::array(Type::Bytes);
        let headers = Type::map(array_bytes);
        let mut builder = crate::SchemeBuilder::new();
        for (name, ty, optional) in [
            ("names", array_bytes, false),
            ("flags", Type::array(Type::Bool), false),
            ("other_flags", Type::array(Type::Bool), false),
            ("text", Type::Bytes, true),
            ("other_text", Type::Bytes, true),
            ("num", Type::Int, true),
            ("other_num", Type::Int, true),
            ("ip", Type::Ip, false),
            ("headers", headers, false),
            ("required", Type::Bytes, false),
        ] {
            if optional {
                builder.add_optional_field(name, ty).unwrap();
            } else {
                builder.add_field(name, ty).unwrap();
            }
        }
        for (name, ty) in [
            ("echo", Type::Bytes),
            ("echo_names", array_bytes),
            ("echo_headers", headers),
        ] {
            builder
                .add_function(
                    name,
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
        builder
            .add_function(
                "owned_names",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }]),
                    opt_params: Box::new([]),
                    return_type: array_bytes,
                    implementation: SimpleFunctionImpl::new(owned_names),
                },
            )
            .unwrap();
        builder
            .add_list(Type::Int, crate::AlwaysList::default())
            .unwrap();
        builder.set_nil_not_equal_behavior(nil_not_equal);
        let scheme = builder.build();
        NativeFields::validate_scheme(&scheme).unwrap();
        let lists = scheme
            .lists()
            .map(|list| list.definition().new_matcher())
            .collect();
        NativeContext {
            scheme,
            names: vec!["Accept".into(), "Other".into(), "".into()],
            flags: vec![true, false, true],
            other_flags: vec![false],
            text: Some("Accept".into()),
            other_text: Some("Other".into()),
            num: Some(7),
            other_num: Some(2),
            ip: "192.0.2.1".parse().unwrap(),
            headers: [
                (
                    Box::from(b"accept".as_slice()),
                    vec!["text/html".into(), "application/json".into()],
                ),
                (Box::from(b"empty".as_slice()), Vec::new()),
            ]
            .into_iter()
            .collect(),
            required: Some("ok".into()),
            lists,
            list_accesses: std::cell::Cell::new(0),
        }
    }

    fn byte_array(values: &[Box<str>]) -> crate::LhsValue<'_> {
        crate::LhsValue::Array(
            crate::Array::try_from_iter(
                crate::Type::Bytes,
                values.iter().map(|s| crate::LhsValue::from(s.as_ref())),
            )
            .unwrap(),
        )
    }

    fn stored_context(ctx: &NativeContext) -> ExecutionContext<'_> {
        use crate::{LhsValue, Type};
        let mut stored = ExecutionContext::new(&ctx.scheme);
        for (name, value) in [
            ("names", byte_array(&ctx.names)),
            (
                "flags",
                crate::Array::try_from_iter(Type::Bool, ctx.flags.iter().copied())
                    .unwrap()
                    .into(),
            ),
            (
                "other_flags",
                crate::Array::try_from_iter(Type::Bool, ctx.other_flags.iter().copied())
                    .unwrap()
                    .into(),
            ),
            ("ip", LhsValue::Ip(ctx.ip)),
            (
                "headers",
                crate::Map::try_from_iter(
                    Type::array(Type::Bytes),
                    ctx.headers.iter().map(|(key, values)| {
                        Ok::<_, crate::TypeMismatchError>((key.clone(), byte_array(values)))
                    }),
                )
                .unwrap()
                .into(),
            ),
        ] {
            stored.set_field_value_from_name(name, value).unwrap();
        }
        for (name, value) in [
            ("text", &ctx.text),
            ("other_text", &ctx.other_text),
            ("required", &ctx.required),
        ] {
            if let Some(value) = value {
                stored
                    .set_field_value_from_name(name, value.as_ref())
                    .unwrap();
            }
        }
        for (name, value) in [("num", ctx.num), ("other_num", ctx.other_num)] {
            if let Some(value) = value {
                stored.set_field_value_from_name(name, value).unwrap();
            }
        }
        stored
    }

    fn compare_filters(ctx: &NativeContext, expressions: &[&str]) {
        let stored = stored_context(ctx);
        let mut compiler = crate::DefaultCompiler::<(), NativeFields>::new();
        for expression in expressions {
            let ast = ctx
                .scheme
                .parse(expression)
                .unwrap_or_else(|error| panic!("{expression}: {error}"));
            let expected = ast.clone().compile().execute(&stored).unwrap();
            let actual = ast
                .compile_with_compiler(&mut compiler)
                .execute(ctx)
                .unwrap();
            assert_eq!(actual, expected, "{expression}");
        }
    }

    #[test]
    fn test_comparison_bindings_use_compiler_hooks_only_during_compilation() {
        struct RecordingCompiler<F> {
            fields: Vec<Box<str>>,
            family: std::marker::PhantomData<F>,
        }

        impl<F: ContextFamily<UserData = ()>> crate::Compiler for RecordingCompiler<F> {
            type Family = F;
            type U = ();

            fn bind_field<B: FieldConsumer<F>>(
                &mut self,
                field: Field,
                consumer: B,
            ) -> Result<B::Output, FieldBindingError> {
                self.fields.push(field.name().into());
                F::bind(field, consumer)
            }
        }

        let context = native_context(true);
        let stored = stored_context(&context);
        let mut native_compiler = RecordingCompiler::<NativeFields> {
            fields: Vec::new(),
            family: std::marker::PhantomData,
        };
        let mut stored_compiler = RecordingCompiler::<super::StoredContextFamily<()>> {
            fields: Vec::new(),
            family: std::marker::PhantomData,
        };

        for (expression, field) in [
            (r#"names[0] == "Accept""#, "names"),
            (r#"any(names[*] == "Accept")"#, "names"),
            (r#"any(headers[*][0] == "text/html")"#, "headers"),
            (r#"any(headers[*][*] == "application/json")"#, "headers"),
        ] {
            let ast = context.scheme.parse(expression).unwrap();
            let native_filter = ast.clone().compile_with_compiler(&mut native_compiler);
            let stored_filter = ast.compile_with_compiler(&mut stored_compiler);
            assert_eq!(native_compiler.fields.len(), 1);
            assert_eq!(native_compiler.fields[0].as_ref(), field);
            assert_eq!(stored_compiler.fields.len(), 1);
            assert_eq!(stored_compiler.fields[0].as_ref(), field);

            for _ in 0..2 {
                assert!(native_filter.execute(&context).unwrap(), "{expression}");
                assert!(stored_filter.execute(&stored).unwrap(), "{expression}");
            }
            assert_eq!(native_compiler.fields.len(), 1);
            assert_eq!(stored_compiler.fields.len(), 1);
            native_compiler.fields.clear();
            stored_compiler.fields.clear();
        }
    }

    #[test]
    fn test_native_complete_operator_and_collection_paths() {
        let ctx = native_context(true);
        compare_filters(
            &ctx,
            &[
                "num == 7",
                "num != 7",
                "num < 8",
                "num <= 7",
                "num > 7",
                "num >= 7",
                "num & 2",
                "num & other_num",
                "num in {1 5..9}",
                "num == other_num",
                r#"text == "Accept""#,
                r#"text != "Accept""#,
                r#"text < "Other""#,
                r#"text contains "cep""#,
                r#"text contains """#,
                r#"text contains "a string longer than the entire field""#,
                r#"text matches "^A.*t$""#,
                r#"text wildcard "a*""#,
                r#"text strict wildcard "a*""#,
                r#"text in {"Other" "Accept"}"#,
                "text == other_text",
                "text > other_text",
                "ip == 192.0.2.1",
                "ip < 192.0.2.2",
                "ip < ::1",
                "ip in {192.0.2.0/24}",
                "any(flags)",
                "all(flags)",
                "any(not flags)",
                "any((flags and other_flags))",
                "any((flags or other_flags))",
                "all((flags xor other_flags))",
                r#"any(names[*] == "Accept")"#,
                r#"all(names[*] != "absent")"#,
                r#"names[0] == "Accept""#,
                r#"names[20] != "absent""#,
                r#"any(headers[*][*] == "text/html")"#,
                r#"headers["accept"][1] == "application/json""#,
                r#"headers["ACCEPT"][0] == "text/html""#,
                r#"all(headers["empty"][*] == "x")"#,
                r#"all(headers["missing"][*] == "x")"#,
                r#"any(echo(names[*])[*] == "Accept")"#,
                r#"any(echo(headers[*][*])[*] == "text/html")"#,
                r#"echo_names(names)[0] == "Accept""#,
                r#"echo_headers(headers)["accept"][0] == "text/html""#,
                r#"any(echo_headers(headers)[*][*] == "text/html")"#,
                r#"owned_names(text)[1] == "Other""#,
                r#"any(owned_names(text)[*] == "Accept")"#,
                "num in $named_list",
            ],
        );
        assert!(ctx.list_accesses.get() > 0);
    }

    #[test]
    fn test_native_and_stored_byte_literal_formats() {
        let ctx = native_context(true);
        let stored = stored_context(&ctx);
        for literal in [r#""Accept""#, r###"r##"Accept"##"###, "41:63:63:65:70:74"] {
            for (operator, expected) in [
                ("==", true),
                ("!=", false),
                ("<=", true),
                (">=", true),
                ("<", false),
                (">", false),
                ("contains", true),
            ] {
                let expression = format!("text {operator} {literal}");
                let ast = ctx.scheme.parse(&expression).unwrap();
                let native = ast
                    .clone()
                    .compile_with_compiler(&mut crate::DefaultCompiler::<(), NativeFields>::new());
                assert_eq!(native.execute(&ctx).unwrap(), expected, "{expression}");
                assert_eq!(
                    ast.compile().execute(&stored).unwrap(),
                    expected,
                    "{expression}"
                );
            }
        }
    }

    #[cfg(feature = "regex")]
    #[test]
    fn test_native_and_stored_regex_literal_formats() {
        let ctx = native_context(true);
        let stored = stored_context(&ctx);
        for literal in [r#""^A.*t$""#, r###"r##"^A.*t$"##"###] {
            for (lhs, expected) in [("text", true), ("other_text", false)] {
                let expression = format!("{lhs} matches {literal}");
                let ast = ctx.scheme.parse(&expression).unwrap();
                let native = ast
                    .clone()
                    .compile_with_compiler(&mut crate::DefaultCompiler::<(), NativeFields>::new());
                assert_eq!(native.execute(&ctx).unwrap(), expected, "{expression}");
                assert_eq!(
                    ast.compile().execute(&stored).unwrap(),
                    expected,
                    "{expression}"
                );
            }
        }
    }

    #[test]
    fn test_native_and_stored_ip_literal_ordering() {
        let mut ctx = native_context(true);
        for (literal, values) in [
            (
                "192.0.2.2",
                ["192.0.2.1", "192.0.2.2", "192.0.2.3", "2001:db8::2"],
            ),
            (
                "2001:db8::2",
                ["2001:db8::1", "2001:db8::2", "2001:db8::3", "192.0.2.2"],
            ),
        ] {
            for (operator, expected) in [
                ("==", [false, true, false, false]),
                ("!=", [true, false, true, true]),
                ("<", [true, false, false, false]),
                ("<=", [true, true, false, false]),
                (">", [false, false, true, false]),
                (">=", [false, true, true, false]),
            ] {
                let expression = format!("ip {operator} {literal}");
                let ast = ctx.scheme.parse(&expression).unwrap();
                let native = ast
                    .clone()
                    .compile_with_compiler(&mut crate::DefaultCompiler::<(), NativeFields>::new());
                let stored = ast.compile();
                for (value, expected) in values.into_iter().zip(expected) {
                    ctx.ip = value.parse().unwrap();
                    assert_eq!(
                        native.execute(&ctx).unwrap(),
                        expected,
                        "{value}: {expression}"
                    );
                    assert_eq!(
                        stored.execute(&stored_context(&ctx)).unwrap(),
                        expected,
                        "{value}: {expression}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_native_general_values_match_stored_values() {
        let ctx = native_context(true);
        let stored = stored_context(&ctx);
        let mut compiler = crate::DefaultCompiler::<(), NativeFields>::new();
        for expression in [
            "text",
            "names",
            "headers",
            "flags",
            "num",
            "ip",
            "echo_names(names)",
            "echo_headers(headers)",
            "echo(names[*])",
            "owned_names(text)",
            "any((flags or other_flags))",
            r#"headers["accept"]"#,
        ] {
            let ast = ctx
                .scheme
                .parse_value(expression)
                .unwrap_or_else(|error| panic!("{expression}: {error}"));
            let expected = ast.clone().compile();
            let actual = ast.compile_with_compiler(&mut compiler);
            assert_eq!(
                actual.execute(&ctx).unwrap(),
                expected.execute(&stored).unwrap(),
                "{expression}"
            );
        }
    }

    #[test]
    fn test_native_dynamic_missing_values_follow_nil_policy() {
        for nil_not_equal in [false, true] {
            for (left, right) in [(true, true), (false, true), (true, false), (false, false)] {
                let mut ctx = native_context(nil_not_equal);
                if !left {
                    ctx.text = None;
                    ctx.num = None;
                }
                if !right {
                    ctx.other_text = None;
                    ctx.other_num = None;
                }
                compare_filters(
                    &ctx,
                    &[
                        "text == other_text",
                        "text != other_text",
                        "text < other_text",
                        "text >= other_text",
                        "num == other_num",
                        "num != other_num",
                        "num < other_num",
                        "num >= other_num",
                        "num & other_num",
                        r#"text != "Accept""#,
                        "any(names[*] == other_text)",
                        "any(names[*] != other_text)",
                        r#"names[50] != "absent""#,
                        r#"any(echo(names[*])[*] == other_text)"#,
                    ],
                );
            }
        }
    }

    #[test]
    fn test_native_required_missing_and_scheme_identity() {
        // Handwritten getters may violate mandatory-field presence even though
        // the field macro rejects optional getters during scheme validation.
        // Retain coverage for the execution-time invariant in that case.
        struct MissingRequiredFields;
        struct RequiredGetter;

        impl ContextFamily for MissingRequiredFields {
            type Context<'data> = NativeContext;
            type UserData = ();

            fn bind<B: FieldConsumer<Self>>(
                field: Field,
                consumer: B,
            ) -> Result<B::Output, FieldBindingError> {
                assert_eq!(field.name(), "required");
                consumer.native(field, RequiredGetter)
            }
        }

        impl super::FieldGetter<MissingRequiredFields> for RequiredGetter {
            type Provider = super::BorrowedValueProvider<str>;

            fn get<'ctx, 'data: 'ctx>(
                &self,
                context: &'ctx NativeContext,
                field: &Field,
            ) -> Option<&'ctx str> {
                assert_eq!(
                    field.as_ref(),
                    context.scheme.get_field("required").unwrap()
                );
                context.required.as_deref()
            }
        }

        let mut ctx = native_context(true);
        let ast = ctx.scheme.parse(r#"required == "ok""#).unwrap();
        let stored_filter = ast.clone().compile();
        let native_filter = ast
            .compile_with_compiler(&mut crate::DefaultCompiler::<(), MissingRequiredFields>::new());
        let different = native_context(true);
        assert_eq!(
            native_filter.execute(&different),
            Err(crate::SchemeMismatchError)
        );
        ctx.required = None;
        let stored = stored_context(&ctx);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || stored_filter.execute(&stored)
            ))
            .is_err()
        );
        let panic =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| native_filter.execute(&ctx)))
                .unwrap_err();
        assert_eq!(
            panic.downcast_ref::<String>().map(String::as_str),
            Some("Field required was registered as mandatory but not given a value")
        );
        compare_filters(&ctx, &[r#"num == 7 or required == "ok""#]);
    }

    #[test]
    fn test_native_value_borrows_invariant_context_for_one_access() {
        use std::cell::Cell;

        struct InvariantContext<'data> {
            scheme: &'data Scheme,
            value: Cell<&'data str>,
        }

        impl super::HasScheme for InvariantContext<'_> {
            fn scheme(&self) -> &Scheme {
                self.scheme
            }
        }

        impl super::EvaluationContext for InvariantContext<'_> {
            type UserData = ();

            fn get_user_data(&self) -> &() {
                &()
            }

            fn get_list_matcher(&self, _: crate::ListRef<'_>) -> &dyn crate::ListMatcher {
                unreachable!("the test scheme has no lists")
            }
        }

        crate::wirefilter_fields! {
            impl<'data> InvariantFields for InvariantContext<'data> {
                "value" => {
                    fn(ctx: &InvariantContext<'data>) -> &str {
                        ctx.value.get()
                    }
                },
            }
        }

        let scheme = Scheme! { value: Bytes }.build();
        InvariantFields::validate_scheme(&scheme).unwrap();
        let filter = scheme
            .parse_value("value")
            .unwrap()
            .compile_with_compiler(&mut crate::DefaultCompiler::<(), InvariantFields>::new());
        let first = Box::<str>::from("first");
        let second = Box::<str>::from("second");
        let mut context = InvariantContext {
            scheme: &scheme,
            value: Cell::new(&first),
        };
        let result = filter.execute(&context).unwrap().unwrap();
        let crate::LhsValue::Bytes(bytes) = result else {
            panic!("expected bytes")
        };
        assert_eq!(bytes.as_ref().as_ptr(), first.as_ptr());
        *context.value.get_mut() = &second;
        assert_eq!(
            filter.execute(&context).unwrap().unwrap(),
            crate::LhsValue::from(second.as_ref())
        );
        assert_eq!(
            std::mem::size_of::<super::ContextRef<'_, '_, InvariantFields>>(),
            std::mem::size_of::<&InvariantContext<'_>>(),
        );
    }

    #[test]
    fn test_native_map_order_matches_materialized_identity_function() {
        let mut context = native_context(true);
        context
            .headers
            .insert(b"z-after".as_slice().into(), vec!["text/html".into()]);
        context
            .headers
            .insert(b"a-before".as_slice().into(), vec!["other".into()]);
        let expression =
            r#"all((headers[*][*] == "text/html" xor echo_headers(headers)[*][*] == "text/html"))"#;
        let stored = stored_context(&context);
        let ast = context.scheme.parse(expression).unwrap();
        let stored_filter = ast.clone().compile();
        let native_filter =
            ast.compile_with_compiler(&mut crate::DefaultCompiler::<(), NativeFields>::new());
        assert!(!stored_filter.execute(&stored).unwrap());
        assert!(!native_filter.execute(&context).unwrap());
    }
}
