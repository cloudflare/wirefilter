//! Default and downstream contexts expose runtime-typed values through native binding.

use std::cell::Cell;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use wirefilter::{
    Array, Compare, CompiledExpr, CompiledValueExpr, Compiler, ContextFamily, DefaultCompiler,
    EvaluationContext, ExecutionContext, Field, FieldBindingError, FieldConsumer,
    FieldDefinitionError, FieldGetter, FieldIndex, FunctionArgs, FunctionCallArgExpr, GetType,
    HasScheme, IdentifierExpr, IndexExpr, LhsValue, LhsValueProvider, ListMatcher, ListRef, Map,
    Scheme, SchemeBuilder, SimpleFunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl,
    SimpleFunctionParam, StoredContextFamily, Type, TypeMismatchError,
};

#[derive(Default)]
struct Reads {
    map: Cell<usize>,
}

struct NativeFields;
struct Getter;

impl ContextFamily for NativeFields {
    type Context<'data> = ExecutionContext<'data, Reads>;
    type UserData = Reads;

    fn bind<B: FieldConsumer<Self>>(
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError> {
        consumer.native(field, Getter)
    }
}

impl FieldGetter<NativeFields> for Getter {
    type Provider = LhsValueProvider;

    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx ExecutionContext<'data, Reads>,
        field: &Field,
    ) -> Option<&'ctx LhsValue<'ctx>> {
        if field.name() == "map" {
            let count = &context.get_user_data().map;
            count.set(count.get() + 1);
        }
        context.get_field_value(field.as_ref())
    }
}

fn array<'a>(ty: Type, values: impl IntoIterator<Item = LhsValue<'a>>) -> LhsValue<'a> {
    Array::try_from_iter(ty, values).unwrap().into()
}

fn map<'a>(ty: Type, entries: impl IntoIterator<Item = (&'a [u8], LhsValue<'a>)>) -> LhsValue<'a> {
    Map::try_from_iter(
        ty,
        entries
            .into_iter()
            .map(|(key, value)| Ok::<_, TypeMismatchError>((key.into(), value))),
    )
    .unwrap()
    .into()
}

fn identity<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    args.next()?.ok()
}

fn add_function(
    builder: &mut SchemeBuilder,
    name: &str,
    params: &[Type],
    return_type: Type,
    implementation: SimpleFunctionImpl,
) {
    builder
        .add_function(
            name,
            SimpleFunctionDefinition {
                params: params
                    .iter()
                    .map(|&val_type| SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type,
                    })
                    .collect(),
                opt_params: Box::new([]),
                return_type,
                implementation,
            },
        )
        .unwrap();
}

fn assert_filter(
    scheme: &Scheme,
    context: &ExecutionContext<'_, Reads>,
    expression: &str,
    expected: bool,
) {
    let ast = scheme.parse(expression).unwrap();
    let default = ast
        .clone()
        .compile_with_compiler(&mut DefaultCompiler::<Reads>::new());
    let native = ast.compile_with_compiler(&mut DefaultCompiler::<Reads, NativeFields>::new());
    assert_eq!(
        default.execute(context).unwrap(),
        expected,
        "default: {expression}"
    );
    assert_eq!(
        native.execute(context).unwrap(),
        expected,
        "native: {expression}"
    );
}

#[test]
fn one_family_handles_all_scalar_types_and_optional_fields() {
    let mut builder = SchemeBuilder::new();
    for (name, ty) in [
        ("number", Type::Int),
        ("text", Type::Bytes),
        ("flag", Type::Bool),
        ("v4", Type::Ip),
        ("v6", Type::Ip),
    ] {
        builder.add_field(name, ty).unwrap();
    }
    builder.add_optional_field("missing", Type::Int).unwrap();
    let scheme = builder.build();
    let mut context = ExecutionContext::new_with(&scheme, Reads::default);
    context.set_field_value_from_name("number", 42i64).unwrap();
    context.set_field_value_from_name("text", "target").unwrap();
    context.set_field_value_from_name("flag", true).unwrap();
    context
        .set_field_value_from_name("v4", IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1)))
        .unwrap();
    context
        .set_field_value_from_name("v6", IpAddr::V6(Ipv6Addr::LOCALHOST))
        .unwrap();
    for (expression, expected) in [
        ("number ge 42", true),
        ("number lt 42", false),
        ("number & 2", true),
        (r#"text eq "target""#, true),
        (r#"text contains "arg""#, true),
        ("flag", true),
        ("not flag", false),
        ("v4 in {192.0.2.0/24}", true),
        ("v6 eq ::1", true),
        ("missing eq 0", false),
        ("missing ne 0", true),
    ] {
        assert_filter(&scheme, &context, expression, expected);
    }
    let native = scheme
        .parse_value("missing")
        .unwrap()
        .compile_with_compiler(&mut DefaultCompiler::<Reads, NativeFields>::new());
    assert_eq!(native.execute(&context).unwrap(), Err(Type::Int));
    assert!(
        context
            .set_field_value_from_name("number", "wrong type")
            .is_err()
    );
}

// Check actual retained element and map-key addresses. Payload-only checks would
// miss rebuilding containers whose byte elements still borrow the source.
fn assert_borrowed_structure(actual: &LhsValue<'_>, original: &LhsValue<'_>) {
    match (actual, original) {
        (LhsValue::Array(actual), LhsValue::Array(original)) => {
            assert_eq!(actual.len(), original.len());
            for (actual, original) in actual.iter().zip(original.iter()) {
                assert!(
                    std::ptr::eq(actual, original),
                    "array elements were rebuilt"
                );
                assert_borrowed_structure(actual, original);
            }
        }
        (LhsValue::Map(actual), LhsValue::Map(original)) => {
            assert_eq!(actual.len(), original.len());
            for ((key, actual), (source_key, original)) in actual.iter().zip(original.iter()) {
                assert_eq!(key, source_key);
                assert_eq!(key.as_ptr(), source_key.as_ptr(), "map key was copied");
                assert!(std::ptr::eq(actual, original), "map values were rebuilt");
                assert_borrowed_structure(actual, original);
            }
        }
        (LhsValue::Bytes(actual), LhsValue::Bytes(original)) => {
            assert_eq!(actual.as_ref(), original.as_ref());
            assert_eq!(actual.as_ref().as_ptr(), original.as_ref().as_ptr());
            assert!(matches!(actual, wirefilter::Bytes::Borrowed(_)));
        }
        _ => assert_eq!(actual, original),
    }
}

#[test]
fn schemes_can_choose_nested_collection_compositions_at_runtime() {
    let payload = String::from("needle");
    // A single ContextFamily/getter handles every composition. No Rust provider
    // specialization is declared for any of these runtime-selected types.
    for depth in 0..=5 {
        for mask in 0..1usize << depth {
            let mut value = LhsValue::from(payload.as_str());
            let mut selection = String::new();
            for level in 0..depth {
                let ty = value.get_type();
                if mask & (1 << level) == 0 {
                    value = array(ty, [value]);
                    selection = format!("[0]{selection}");
                } else {
                    value = map(ty, [(b"k".as_slice(), value)]);
                    selection = format!("[\"k\"]{selection}");
                }
            }
            let ty = value.get_type();
            let mut builder = SchemeBuilder::new();
            builder.add_field("value", ty).unwrap();
            add_function(
                &mut builder,
                "echo",
                &[ty],
                ty,
                SimpleFunctionImpl::new(identity),
            );
            let scheme = builder.build();
            let mut context = ExecutionContext::new_with(&scheme, Reads::default);
            context.set_field_value_from_name("value", value).unwrap();
            assert_filter(
                &scheme,
                &context,
                &format!("value{selection} eq \"needle\""),
                true,
            );
            if depth > 0 {
                assert_filter(
                    &scheme,
                    &context,
                    &format!("any(value{} eq \"needle\")", "[*]".repeat(depth)),
                    true,
                );
            }
            let ast = scheme.parse_value("echo(value)").unwrap();
            let default = ast
                .clone()
                .compile_with_compiler(&mut DefaultCompiler::<Reads>::new());
            let custom =
                ast.compile_with_compiler(&mut DefaultCompiler::<Reads, NativeFields>::new());
            let original = context
                .get_field_value(scheme.get_field("value").unwrap())
                .unwrap();
            for actual in [default.execute(&context), custom.execute(&context)] {
                assert_borrowed_structure(&actual.unwrap().unwrap(), original);
            }
        }
    }
}

#[test]
fn indexed_and_mapped_arguments_preserve_missing_values_and_map_compatibility() {
    let bytes_array = Type::array(Type::Bytes);
    let mut builder = SchemeBuilder::new();
    builder.add_field("map", Type::map(bytes_array)).unwrap();
    builder
        .add_optional_field("absent", Type::map(bytes_array))
        .unwrap();
    add_function(
        &mut builder,
        "echo_bytes",
        &[Type::Bytes],
        Type::Bytes,
        SimpleFunctionImpl::new(identity),
    );
    add_function(
        &mut builder,
        "echo_array",
        &[bytes_array],
        bytes_array,
        SimpleFunctionImpl::new(identity),
    );
    let scheme = builder.build();
    let payload = String::from("payload");
    let mut context = ExecutionContext::new_with(&scheme, Reads::default);
    context
        .set_field_value_from_name(
            "map",
            map(
                bytes_array,
                [
                    (
                        b"a".as_slice(),
                        array(Type::Bytes, [payload.as_str().into()]),
                    ),
                    (b"empty".as_slice(), array(Type::Bytes, [])),
                ],
            ),
        )
        .unwrap();
    for (expression, expected) in [
        (
            r#"echo_array(map["a"])"#,
            Ok(array(Type::Bytes, [payload.as_str().into()])),
        ),
        (r#"echo_array(map["missing"])"#, Err(bytes_array)),
        (r#"echo_bytes(map["a"][0])"#, Ok(payload.as_str().into())),
        (r#"echo_bytes(map["a"][8])"#, Err(Type::Bytes)),
        (
            r#"echo_bytes(map["a"][*])"#,
            Ok(array(Type::Bytes, [payload.as_str().into()])),
        ),
        (
            "echo_bytes(map[*][*])",
            Ok(array(Type::Bytes, [payload.as_str().into()])),
        ),
        ("echo_bytes(absent[*][*])", Err(bytes_array)),
        (r#"echo_bytes(map["missing"][*])"#, Err(bytes_array)),
        (r#"echo_bytes(map["empty"][*])"#, Ok(array(Type::Bytes, []))),
    ] {
        let ast = scheme.parse_value(expression).unwrap();
        let default = ast
            .clone()
            .compile_with_compiler(&mut DefaultCompiler::<Reads>::new());
        let native = ast.compile_with_compiler(&mut DefaultCompiler::<Reads, NativeFields>::new());
        assert_eq!(
            default.execute(&context).unwrap(),
            expected,
            "default: {expression}"
        );
        assert_eq!(
            native.execute(&context).unwrap(),
            expected,
            "custom: {expression}"
        );
    }

    let ast = scheme.parse_value(r#"echo_array(map["a"])"#).unwrap();
    let default = ast
        .clone()
        .compile_with_compiler(&mut DefaultCompiler::<Reads>::new());
    let custom = ast.compile_with_compiler(&mut DefaultCompiler::<Reads, NativeFields>::new());
    let LhsValue::Map(original) = context
        .get_field_value(scheme.get_field("map").unwrap())
        .unwrap()
    else {
        unreachable!()
    };
    for selected in [default.execute(&context), custom.execute(&context)] {
        assert_borrowed_structure(&selected.unwrap().unwrap(), original.get(b"a").unwrap());
    }

    struct ObserveMapArgument {
        arguments: usize,
    }
    impl Compiler for ObserveMapArgument {
        type Family = StoredContextFamily<Reads>;
        type U = Reads;

        fn compile_function_call_arg_expr(
            &mut self,
            node: FunctionCallArgExpr,
        ) -> CompiledValueExpr<Reads> {
            self.arguments += 1;
            let value = self.compile_value_expr(node);
            CompiledValueExpr::new_with_context(move |ctx| {
                let result = value.execute(ctx.context());
                assert!(
                    matches!(&result, Ok(LhsValue::Map(_))),
                    "trailing map[*] changed the compiler hook's value"
                );
                result
            })
        }
    }
    let mut compiler = ObserveMapArgument { arguments: 0 };
    let actual = scheme
        .parse_value("echo_array(map[*])")
        .unwrap()
        .compile_with_compiler(&mut compiler);
    assert_eq!(compiler.arguments, 1);
    let expected = scheme
        .parse_value("echo_array(map[*])")
        .unwrap()
        .compile_with_compiler(&mut DefaultCompiler::<Reads>::new());
    assert_eq!(actual.execute(&context), expected.execute(&context));
}

fn record_children(value: &LhsValue<'_>, addresses: &mut Vec<usize>) {
    match value {
        LhsValue::Array(array) => {
            for value in array.iter() {
                addresses.push(std::ptr::from_ref(value) as usize);
                record_children(value, addresses);
            }
        }
        LhsValue::Map(map) => {
            for (_, value) in map.iter() {
                addresses.push(std::ptr::from_ref(value) as usize);
                record_children(value, addresses);
            }
        }
        _ => {}
    }
}

struct OriginalCollection {
    children: Vec<usize>,
}
impl<F: ContextFamily<UserData = Reads>> Compare<Reads, F> for OriginalCollection {
    fn compare<'ctx, 'data: 'ctx>(
        &self,
        value: &LhsValue<'ctx>,
        _: &'ctx F::Context<'data>,
    ) -> bool {
        let first = match value {
            LhsValue::Array(array) => array.get(0),
            LhsValue::Map(map) => map.iter().next().map(|(_, value)| value),
            _ => panic!("custom comparison requires a collection"),
        };
        if let Some(first) = first {
            assert!(
                self.children
                    .contains(&(std::ptr::from_ref(first) as usize)),
                "custom comparison received a rebuilt collection"
            );
            true
        } else {
            false
        }
    }
}

#[test]
fn compiler_comparisons_can_borrow_selected_collections() {
    let bytes = Type::array(Type::Bytes);
    let mut builder = SchemeBuilder::new();
    builder
        .add_field("rows", Type::array(Type::map(bytes)))
        .unwrap();
    let scheme = builder.build();
    let value = array(
        Type::map(bytes),
        [
            map(
                bytes,
                [(b"key".as_slice(), array(Type::Bytes, ["value".into()]))],
            ),
            map(bytes, []),
        ],
    );
    let mut context = ExecutionContext::new_with(&scheme, Reads::default);
    context.set_field_value_from_name("rows", value).unwrap();
    let mut children = Vec::new();
    record_children(
        context
            .get_field_value(scheme.get_field("rows").unwrap())
            .unwrap(),
        &mut children,
    );
    for indexes in [
        vec![],
        vec![FieldIndex::ArrayIndex(0)],
        vec![FieldIndex::ArrayIndex(0), FieldIndex::MapKey("key".into())],
        vec![FieldIndex::ArrayIndex(8)],
        vec![FieldIndex::MapEach],
        vec![FieldIndex::MapEach, FieldIndex::MapEach],
    ] {
        for missing_default in [false, true] {
            let index = IndexExpr {
                identifier: IdentifierExpr::Field(scheme.get_field("rows").unwrap().to_owned()),
                indexes: indexes.clone().into_boxed_slice(),
            };
            let default = index.clone().compile_with(
                &mut DefaultCompiler::<Reads>::new(),
                missing_default,
                OriginalCollection {
                    children: children.clone(),
                },
            );
            let native = index.compile_with(
                &mut DefaultCompiler::<Reads, NativeFields>::new(),
                missing_default,
                OriginalCollection {
                    children: children.clone(),
                },
            );
            match (default, native) {
                (CompiledExpr::One(default), CompiledExpr::One(native)) => {
                    assert_eq!(default.execute(&context), native.execute(&context))
                }
                (CompiledExpr::Vec(default), CompiledExpr::Vec(native)) => {
                    assert_eq!(default.execute(&context), native.execute(&context))
                }
                _ => panic!("comparison cardinality changed"),
            }
        }
    }
}

#[test]
fn mapped_extra_stored_arguments_keep_cheap_lazy_access() {
    fn consume_both<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()?;
        args.next()?.ok()?;
        Some(true.into())
    }
    fn consume_first<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()?;
        Some(true.into())
    }
    let mut builder = SchemeBuilder::new();
    builder
        .add_optional_field("numbers", Type::array(Type::Int))
        .unwrap();
    builder.add_field("map", Type::map(Type::Int)).unwrap();
    for (name, extra, implementation) in [
        (
            "map_arg",
            Type::map(Type::Int),
            consume_both as for<'i, 'a> fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>>,
        ),
        ("int_arg", Type::Int, consume_both),
        ("ignore_map", Type::map(Type::Int), consume_first),
    ] {
        add_function(
            &mut builder,
            name,
            &[Type::Int, extra],
            Type::Bool,
            SimpleFunctionImpl::new(implementation),
        );
    }
    let scheme = builder.build();
    let mut context = ExecutionContext::new_with(&scheme, Reads::default);
    context
        .set_field_value_from_name("numbers", array(Type::Int, [1.into(), 2.into(), 3.into()]))
        .unwrap();
    context
        .set_field_value_from_name("map", map(Type::Int, [(b"key".as_slice(), 7.into())]))
        .unwrap();
    for expression in [
        "any(map_arg(numbers[*], map))",
        r#"any(int_arg(numbers[*], map["key"]))"#,
    ] {
        let native = scheme
            .parse(expression)
            .unwrap()
            .compile_with_compiler(&mut DefaultCompiler::<Reads, NativeFields>::new());
        context.get_user_data().map.set(0);
        assert!(native.execute(&context).unwrap());
        // Repeated cheap borrowing is intentional. Treating this provider as a
        // materializing native collection would read once and allocate caches.
        assert_eq!(context.get_user_data().map.get(), 3, "{expression}");
    }
    // Leaving the mandatory map absent proves ignored arguments stay unread.
    let mut missing = ExecutionContext::new_with(&scheme, Reads::default);
    missing
        .set_field_value_from_name("numbers", array(Type::Int, [1.into(), 2.into()]))
        .unwrap();
    assert_filter(&scheme, &missing, "any(ignore_map(numbers[*], map))", true);
    assert_eq!(missing.get_user_data().map.get(), 0);
    missing
        .set_field_value_from_name("numbers", array(Type::Int, []))
        .unwrap();
    assert_filter(&scheme, &missing, "any(map_arg(numbers[*], map))", false);
    assert_eq!(missing.get_user_data().map.get(), 0);
}

struct BorrowingContext<'data> {
    scheme: &'data Scheme,
    value: LhsValue<'data>,
    optional: Option<LhsValue<'data>>,
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
        unreachable!()
    }
}
wirefilter::wirefilter_fields! {
    impl<'data> BorrowingFields for BorrowingContext<'data> {
        "value" => {
            provider LhsValueProvider;
            fn(ctx: &BorrowingContext<'data>) -> &LhsValue<'data> { &ctx.value }
        },
        "optional" => {
            provider LhsValueProvider;
            fn(ctx: &BorrowingContext<'data>) -> Option<&LhsValue<'data>> { ctx.optional.as_ref() }
        },
    }
}

#[test]
fn macro_supports_borrowed_runtime_values_and_validates_presence() {
    let mut builder = SchemeBuilder::new();
    builder.add_field("value", Type::Bytes).unwrap();
    builder.add_optional_field("optional", Type::Int).unwrap();
    let scheme = builder.build();
    BorrowingFields::validate_scheme(&scheme).unwrap();
    let payload = String::from("borrowed");
    let context = BorrowingContext {
        scheme: &scheme,
        value: payload.as_str().into(),
        optional: None,
    };
    let filter = scheme
        .parse(r#"value eq "borrowed" and optional ne 1"#)
        .unwrap()
        .compile_with_compiler(&mut DefaultCompiler::<(), BorrowingFields>::new());
    assert!(filter.execute(&context).unwrap());
    let value = scheme
        .parse_value("value")
        .unwrap()
        .compile_with_compiler(&mut DefaultCompiler::<(), BorrowingFields>::new())
        .execute(&context)
        .unwrap()
        .unwrap();
    assert_borrowed_structure(&value, &context.value);

    let mut builder = SchemeBuilder::new();
    builder.add_field("value", Type::Bytes).unwrap();
    builder.add_field("optional", Type::Int).unwrap();
    let errors = BorrowingFields::validate_scheme(&builder.build()).unwrap_err();
    assert!(errors.0.iter().any(|error| matches!(error, FieldDefinitionError::OptionalGetterForMandatoryField(name) if name.as_ref() == "optional")));

    // These same getters can serve another scheme's runtime-selected types.
    let mut builder = SchemeBuilder::new();
    builder.add_field("value", Type::Int).unwrap();
    builder.add_optional_field("optional", Type::Bytes).unwrap();
    let scheme = builder.build();
    BorrowingFields::validate_scheme(&scheme).unwrap();
    let context = BorrowingContext {
        scheme: &scheme,
        value: 42.into(),
        optional: Some("present".into()),
    };
    let filter = scheme
        .parse(r#"value eq 42 and optional eq "present""#)
        .unwrap()
        .compile_with_compiler(&mut DefaultCompiler::<(), BorrowingFields>::new());
    assert!(filter.execute(&context).unwrap());

    let mut builder = SchemeBuilder::new();
    builder.add_field("value", Type::Int).unwrap();
    builder.add_optional_field("optional", Type::Bytes).unwrap();
    builder.add_field("undefined", Type::Bool).unwrap();
    let errors = BorrowingFields::validate_scheme(&builder.build()).unwrap_err();
    assert!(errors.0.iter().any(|error| matches!(error, FieldDefinitionError::MissingGetter(name) if name.as_ref() == "undefined")));
}
