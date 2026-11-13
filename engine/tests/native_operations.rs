#![cfg(feature = "bytes")]

use bytes::Bytes;
use std::any::TypeId;
use std::cell::Cell;
use wirefilter::native::values::{self, IntoLhsValue, SliceView};
use wirefilter::{
    Compiler, ContextFamily, ContextRef, DefaultCompiler, EvaluationContext, Field,
    FieldBindingError, FieldConsumer, FieldGetter, FieldIndex, HasScheme, IdentifierExpr,
    IndexExpr, LhsValue, ListMatcher, ListRef, ProviderFamily, Scheme, SchemeBuilder, Type,
    ValueExpr,
};

// Cell makes the context invariant in 'data. The descriptor borrows the request
// storage for 'data, rather than being tied to a temporary getter result.
struct BorrowingContext<'data> {
    scheme: &'data Scheme,
    rows: Cell<&'data [Vec<Bytes>]>,
    getter_calls: Cell<usize>,
}

impl HasScheme for BorrowingContext<'_> {
    fn scheme(&self) -> &Scheme {
        self.scheme
    }
}

impl EvaluationContext for BorrowingContext<'_> {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        &()
    }

    fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
        unreachable!("no list matchers in this test")
    }
}

struct RowsProvider;

impl ProviderFamily for RowsProvider {
    type Storage<'data> = &'data [Vec<Bytes>];
    type Value<'ctx, 'data>
        = SliceView<'data, Vec<Bytes>>
    where
        'data: 'ctx;
    type ValueType = values::Array<values::Array<values::Bytes>>;

    fn reborrow<'ctx, 'data: 'ctx>(value: &'ctx Self::Storage<'data>) -> Self::Value<'ctx, 'data> {
        SliceView(value)
    }
}

wirefilter::wirefilter_fields! {
    impl<'data> BorrowingFields for BorrowingContext<'data> {
        "rows" => {
            provider RowsProvider;
            fn(ctx: &BorrowingContext<'data>, field: &Field) -> SliceView<'data, Vec<Bytes>> {
                assert_eq!(field.name(), "rows");
                ctx.getter_calls.set(ctx.getter_calls.get() + 1);
                SliceView(ctx.rows.get())
            }
        },
        "first" => {
            provider RowsProvider;
            fn(ctx: &BorrowingContext<'data>, field: &Field) -> SliceView<'data, Vec<Bytes>> {
                assert_eq!(field.name(), "first");
                assert!(!field.optional());
                ctx.getter_calls.set(ctx.getter_calls.get() + 1);
                let rows = ctx.rows.get();
                SliceView(&rows[..rows.len().min(1)])
            }
        },
        "optional" => {
            provider RowsProvider;
            fn(ctx: &BorrowingContext<'data>, field: &Field) -> Option<SliceView<'data, Vec<Bytes>>> {
                assert_eq!(field.name(), "optional");
                ctx.getter_calls.set(ctx.getter_calls.get() + 1);
                let rows = ctx.rows.get();
                (!rows.is_empty()).then_some(SliceView(rows))
            }
        },
    }
}

#[derive(Default)]
struct RecordingCompiler {
    bindings: Vec<String>,
}

impl Compiler for RecordingCompiler {
    type Family = BorrowingFields;
    type U = ();

    fn bind_field<B: FieldConsumer<BorrowingFields>>(
        &mut self,
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError> {
        self.bindings.push(field.name().into());
        BorrowingFields::bind(field, consumer)
    }
}

fn scheme() -> Scheme {
    let mut builder = SchemeBuilder::new();
    let rows = Type::array(Type::array(Type::Bytes));
    builder.add_field("rows", rows).unwrap();
    builder.add_field("first", rows).unwrap();
    builder.add_optional_field("optional", rows).unwrap();
    let scheme = builder.build();
    BorrowingFields::validate_scheme(&scheme).unwrap();
    scheme
}

#[test]
fn test_same_provider_and_presence_getters_share_a_type_and_preserve_field_selection() {
    type ReadValue = Box<
        dyn for<'ctx, 'data> Fn(ContextRef<'ctx, 'data, BorrowingFields>) -> Option<LhsValue<'ctx>>,
    >;

    struct ReadConsumer;

    impl FieldConsumer<BorrowingFields> for ReadConsumer {
        type Output = (TypeId, ReadValue);

        fn consume<G: FieldGetter<BorrowingFields>>(
            self,
            field: Field,
            getter: G,
        ) -> Result<Self::Output, FieldBindingError> {
            let read: ReadValue = Box::new(move |context| {
                let value = {
                    let metadata = field.clone();
                    getter.get(context.context(), &metadata)
                };
                // Dropping the independently borrowed field metadata must not
                // prevent retaining the native value's request references.
                value.map(IntoLhsValue::into_lhs)
            });
            Ok((TypeId::of::<G>(), read))
        }
    }

    let scheme = scheme();
    let (required_type, required) =
        BorrowingFields::bind(scheme.get_field("rows").unwrap().to_owned(), ReadConsumer).unwrap();
    let (first_type, first) =
        BorrowingFields::bind(scheme.get_field("first").unwrap().to_owned(), ReadConsumer).unwrap();
    let (optional_type, optional) = BorrowingFields::bind(
        scheme.get_field("optional").unwrap().to_owned(),
        ReadConsumer,
    )
    .unwrap();
    assert_eq!(required_type, first_type);
    assert_ne!(required_type, optional_type);

    let rows = [
        vec![Bytes::from_static(b"first payload")],
        vec![Bytes::from_static(b"second payload")],
    ];
    let context = BorrowingContext {
        scheme: &scheme,
        rows: Cell::new(rows.as_slice()),
        getter_calls: Cell::new(0),
    };
    let required_value = required(ContextRef::new(&context)).unwrap();
    let optional_value = optional(ContextRef::new(&context)).unwrap();
    assert_eq!(required_value, optional_value);
    let first_value = first(ContextRef::new(&context)).unwrap();
    assert_eq!(first_value, SliceView(&rows[..1]).into_lhs());
    assert_ne!(required_value, first_value);
    assert_eq!(context.getter_calls.get(), 3);

    context.rows.set(&[]);
    assert!(required(ContextRef::new(&context)).is_some());
    assert!(first(ContextRef::new(&context)).is_some());
    assert!(optional(ContextRef::new(&context)).is_none());
    assert_eq!(context.getter_calls.get(), 6);
}

#[test]
fn descriptor_comparisons_borrow_invariant_context_and_preserve_getter_hooks() {
    let scheme = scheme();
    let first = [
        vec![Bytes::from_static(b"first"), Bytes::from_static(b"target")],
        vec![],
    ];
    let second = [
        vec![Bytes::from_static(b"second")],
        vec![Bytes::from_static(b"target")],
    ];
    let context = BorrowingContext {
        scheme: &scheme,
        rows: Cell::new(first.as_slice()),
        getter_calls: Cell::new(0),
    };
    let mut compiler = RecordingCompiler::default();
    for (expression, field, expected_first, expected_second) in [
        (r#"rows[0][0] eq "first""#, "rows", true, false),
        (r#"any(rows[0][*] eq "target")"#, "rows", true, false),
        (r#"any(rows[*][*] eq "target")"#, "rows", true, true),
        (r#"any(rows[*][0] eq "target")"#, "rows", false, true),
        (r#"optional[0][0] eq "first""#, "optional", true, false),
        (r#"any(optional[*][*] eq "target")"#, "optional", true, true),
    ] {
        let binding_count = compiler.bindings.len();
        let filter = scheme
            .parse(expression)
            .unwrap()
            .compile_with_compiler(&mut compiler);
        assert_eq!(&compiler.bindings[binding_count..], &[field]);
        for (rows, expected) in [
            (first.as_slice(), expected_first),
            (second.as_slice(), expected_second),
            ([].as_slice(), false),
        ] {
            context.rows.set(rows);
            let getter_count = context.getter_calls.get();
            assert_eq!(filter.execute(&context).unwrap(), expected, "{expression}");
            assert_eq!(context.getter_calls.get(), getter_count + 1);
            assert_eq!(compiler.bindings.len(), binding_count + 1);
        }
    }
}

#[test]
fn descriptor_materialization_keeps_payloads_borrowed_from_invariant_context() {
    let scheme = scheme();
    let rows = [vec![
        Bytes::from_static(b"first"),
        Bytes::from_static(b"second"),
    ]];
    let context = BorrowingContext {
        scheme: &scheme,
        rows: Cell::new(rows.as_slice()),
        getter_calls: Cell::new(0),
    };
    let mut compiler = DefaultCompiler::<(), BorrowingFields>::new();
    // The public IndexExpr API supports general `[*]` selections used by
    // mapped function arguments; parse_value rejects this top-level `[*]`.
    for indexes in [
        vec![],
        vec![FieldIndex::ArrayIndex(0), FieldIndex::ArrayIndex(0)],
        vec![FieldIndex::MapEach, FieldIndex::MapEach],
    ] {
        let expression = IndexExpr {
            identifier: IdentifierExpr::Field(scheme.get_field("rows").unwrap().to_owned()),
            indexes: indexes.into_boxed_slice(),
        };
        let filter = expression.compile_with_compiler(&mut compiler);
        let getter_count = context.getter_calls.get();
        let value = filter.execute(&context).unwrap();
        let bytes = match &value {
            LhsValue::Bytes(bytes) => bytes,
            LhsValue::Array(array) => match array.get(0).unwrap() {
                LhsValue::Bytes(bytes) => bytes,
                LhsValue::Array(array) => match array.get(0).unwrap() {
                    LhsValue::Bytes(bytes) => bytes,
                    _ => panic!("expected nested bytes"),
                },
                _ => panic!("expected bytes or array"),
            },
            _ => panic!("unexpected materialized value"),
        };
        assert_eq!(bytes.as_ref().as_ptr(), rows[0][0].as_ptr());
        assert_eq!(context.getter_calls.get(), getter_count + 1);
    }
}
