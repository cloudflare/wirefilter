//! Startup validation for context families implemented without the field macro.

use std::cell::RefCell;
use std::collections::BTreeMap;
use wirefilter::{
    BorrowedValueProvider, ContextFamily, ExecutionContext, Field, FieldBindingError,
    FieldConsumer, FieldDefinitionError, FieldGetter, LhsValue, LhsValueProvider,
    OwnedValueProvider, Scheme, SchemeBuilder, SchemeValidationError, Type,
};

thread_local! {
    static BINDINGS: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

struct Fields;
struct IntegerGetter;
struct HeadersGetter;
struct StoredGetter;

type Headers = BTreeMap<Box<[u8]>, Vec<String>>;

impl ContextFamily for Fields {
    type Context<'data> = ExecutionContext<'data>;
    type UserData = ();

    fn bind<B: FieldConsumer<Self>>(
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError> {
        BINDINGS.with_borrow_mut(|bindings| bindings.push(field.name().into()));
        match field.name() {
            "count" | "after_errors" => consumer.consume(field, IntegerGetter),
            "headers" => consumer.consume(field, HeadersGetter),
            "stored_scalar" | "stored_collection" => consumer.consume(field, StoredGetter),
            "unsupported" => Err(FieldBindingError::Unsupported(
                "application binding rejected",
            )),
            name => Err(FieldBindingError::UnknownField(name.into())),
        }
    }
}

impl FieldGetter<Fields> for IntegerGetter {
    type Provider = OwnedValueProvider<i64>;

    fn get<'ctx, 'data: 'ctx>(&self, _: &'ctx ExecutionContext<'data>, _: &Field) -> Option<i64> {
        panic!("scheme validation must not read integer values")
    }
}

impl FieldGetter<Fields> for HeadersGetter {
    type Provider = BorrowedValueProvider<Headers>;

    fn get<'ctx, 'data: 'ctx>(
        &self,
        _: &'ctx ExecutionContext<'data>,
        _: &Field,
    ) -> Option<&'ctx Headers> {
        panic!("scheme validation must not read header values")
    }
}

impl FieldGetter<Fields> for StoredGetter {
    type Provider = LhsValueProvider;

    fn get<'ctx, 'data: 'ctx>(
        &self,
        _: &'ctx ExecutionContext<'data>,
        _: &Field,
    ) -> Option<&'ctx LhsValue<'ctx>> {
        panic!("scheme validation must not read stored values")
    }
}

fn validate(scheme: &Scheme) -> Result<(), SchemeValidationError> {
    BINDINGS.with_borrow_mut(Vec::clear);
    let result = Fields::validate_scheme(scheme);
    let bindings = BINDINGS.with_borrow_mut(std::mem::take);
    let expected: Vec<_> = scheme
        .fields()
        .map(|field| field.name().to_owned())
        .collect();
    assert_eq!(
        bindings, expected,
        "every scheme field must bind exactly once"
    );
    result
}

#[test]
fn default_validation_checks_scalar_and_nested_collection_types_without_reading_values() {
    let mut builder = SchemeBuilder::new();
    builder.add_field("count", Type::Int).unwrap();
    builder
        .add_optional_field("headers", Type::map(Type::array(Type::Bytes)))
        .unwrap();

    // No request context or field values are needed for validation.
    assert_eq!(validate(&builder.build()), Ok(()));
}

#[test]
fn default_validation_aggregates_binding_errors_for_unused_and_optional_fields() {
    let mut builder = SchemeBuilder::new();
    builder.add_field("count", Type::Bytes).unwrap();
    builder
        .add_field("headers", Type::map(Type::array(Type::Int)))
        .unwrap();
    builder.add_field("missing", Type::Int).unwrap();
    builder
        .add_optional_field("missing_optional", Type::Bool)
        .unwrap();
    builder.add_field("unsupported", Type::Bool).unwrap();
    builder.add_field("after_errors", Type::Int).unwrap();

    // No filter references these fields: startup checks the complete scheme.
    let errors = validate(&builder.build()).unwrap_err();
    let expected = [
        (
            "count",
            FieldBindingError::TypeMismatch {
                field: "count".into(),
                expected: Type::Bytes,
                actual: Type::Int,
            },
        ),
        (
            "headers",
            FieldBindingError::TypeMismatch {
                field: "headers".into(),
                expected: Type::map(Type::array(Type::Int)),
                actual: Type::map(Type::array(Type::Bytes)),
            },
        ),
        ("missing", FieldBindingError::UnknownField("missing".into())),
        (
            "missing_optional",
            FieldBindingError::UnknownField("missing_optional".into()),
        ),
        (
            "unsupported",
            FieldBindingError::Unsupported("application binding rejected"),
        ),
    ]
    .into_iter()
    .map(|(name, error)| FieldDefinitionError::Binding {
        name: name.into(),
        error,
    })
    .collect::<Box<[_]>>();
    assert_eq!(errors, SchemeValidationError(expected));
}

#[test]
fn default_validation_accepts_runtime_typed_providers_without_reading_values() {
    let mut builder = SchemeBuilder::new();
    builder.add_field("stored_scalar", Type::Ip).unwrap();
    builder
        .add_optional_field("stored_collection", Type::array(Type::map(Type::Bool)))
        .unwrap();

    // LhsValueProvider has no static type; its context must check actual values.
    assert_eq!(validate(&builder.build()), Ok(()));
}
