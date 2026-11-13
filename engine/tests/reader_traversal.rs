//! Traversal must preserve ownership as well as selection and comparison results.

use std::cell::RefCell;
use std::collections::BTreeMap;
use wirefilter::{
    Array, Bytes, Compare, CompiledExpr, CompiledValueExpr, ContextFamily, DefaultCompiler,
    EvaluationContext, ExecutionContext, FieldIndex, FilterValueExpr, FunctionArgs, HasScheme,
    IdentifierExpr, IndexExpr, LhsValue, ListMatcher, ListRef, Map, NativeContextState, Scheme,
    SchemeBuilder, SimpleFunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl,
    SimpleFunctionParam, Type, TypeMismatchError, ValueExpr,
};

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

fn add_function(
    builder: &mut SchemeBuilder,
    name: &str,
    parameters: &[Type],
    output: Type,
    implementation: SimpleFunctionImpl,
) {
    builder
        .add_function(
            name,
            SimpleFunctionDefinition {
                params: parameters
                    .iter()
                    .map(|&val_type| SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type,
                    })
                    .collect(),
                opt_params: Box::new([]),
                return_type: output,
                implementation,
            },
        )
        .unwrap();
}

fn compile_selection(scheme: &Scheme, call: &str, indexes: Vec<FieldIndex>) -> CompiledValueExpr {
    // Bare [*] value expressions are not accepted as a FilterValueAst. Construct
    // the same IndexExpr node that occurs within a mapped function argument.
    let FilterValueExpr::Index(mut index) = scheme.parse_value(call).unwrap().expression().clone()
    else {
        panic!("expected function-call index expression")
    };
    index.indexes = indexes.into_boxed_slice();
    index.compile()
}

thread_local! {
    // Record the allocations produced inside the function, before its temporary
    // outer containers are consumed by index selection.
    static GENERATED: RefCell<Vec<(Vec<u8>, usize)>> = const { RefCell::new(Vec::new()) };
}

fn owned_bytes(text: &str) -> LhsValue<'static> {
    let bytes = text.as_bytes().to_vec().into_boxed_slice();
    GENERATED.with_borrow_mut(|records| {
        records.push((text.as_bytes().to_vec(), bytes.as_ptr() as usize));
    });
    LhsValue::Bytes(Bytes::Owned(bytes))
}

fn owned_rows<'a>(_: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    GENERATED.with_borrow_mut(Vec::clear);
    Some(map(
        Type::array(Type::Bytes),
        [
            (
                b"z".as_slice(),
                array(Type::Bytes, [owned_bytes("z0"), owned_bytes("z1")]),
            ),
            (b"a".as_slice(), array(Type::Bytes, [owned_bytes("a0")])),
            (b"empty".as_slice(), array(Type::Bytes, [])),
        ],
    ))
}

fn absent<'a>(_: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    None
}

fn identity<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    args.next()?.ok()
}

fn assert_original_owned_payload(value: &LhsValue<'_>) {
    match value {
        LhsValue::Bytes(Bytes::Owned(bytes)) => GENERATED.with_borrow(|records| {
            let (_, address) = records
                .iter()
                .find(|(text, _)| text.as_slice() == bytes.as_ref())
                .unwrap();
            assert_eq!(
                bytes.as_ptr() as usize,
                *address,
                "owned payload was copied"
            );
        }),
        LhsValue::Array(values) => {
            for value in values.iter() {
                assert_original_owned_payload(value);
            }
        }
        value => panic!("expected retained owned bytes, got {value:?}"),
    }
}

#[test]
fn selections_move_owned_function_payloads_and_preserve_map_order() {
    use FieldIndex::{ArrayIndex, MapEach, MapKey};

    let mut builder = SchemeBuilder::new();
    let rows = Type::map(Type::array(Type::Bytes));
    add_function(
        &mut builder,
        "owned_rows",
        &[],
        rows,
        SimpleFunctionImpl::new(owned_rows),
    );
    add_function(
        &mut builder,
        "absent",
        &[],
        rows,
        SimpleFunctionImpl::new(absent),
    );
    let scheme = builder.build();
    let context = ExecutionContext::new(&scheme);
    for (indexes, expected) in [
        (
            vec![MapEach, MapEach],
            array(Type::Bytes, ["a0".into(), "z0".into(), "z1".into()]),
        ),
        (
            vec![MapEach, ArrayIndex(0)],
            array(Type::Bytes, ["a0".into(), "z0".into()]),
        ),
        (
            vec![MapKey("z".into()), MapEach],
            array(Type::Bytes, ["z0".into(), "z1".into()]),
        ),
        (vec![MapKey("z".into()), ArrayIndex(1)], "z1".into()),
        (vec![MapEach, ArrayIndex(9)], array(Type::Bytes, [])),
    ] {
        // Selection consumes the function's temporary root. The compiled
        // expression is also dropped before the selected payloads are inspected.
        let result = {
            let filter = compile_selection(&scheme, "owned_rows()", indexes.clone());
            filter.execute(&context).unwrap()
        };
        assert_eq!(result, expected, "{indexes:?}");
        assert_original_owned_payload(&result);
    }
    for (call, indexes, expected) in [
        (
            "owned_rows()",
            vec![MapKey("missing".into()), MapEach],
            Type::array(Type::Bytes),
        ),
        ("absent()", vec![MapEach, MapEach], Type::array(Type::Bytes)),
        (
            "absent()",
            vec![MapKey("z".into()), ArrayIndex(0)],
            Type::Bytes,
        ),
    ] {
        let filter = compile_selection(&scheme, call, indexes);
        assert_eq!(filter.execute(&context), Err(expected), "{call}");
    }
    for (expression, expected) in [
        (r#"any(owned_rows()[*][*] eq "z1")"#, true),
        (r#"all(owned_rows()[*][*] eq "z1")"#, false),
        (r#"owned_rows()["z"][0] eq "z0""#, true),
        (r#"owned_rows()["missing"][0] eq "x""#, false),
        (r#"owned_rows()["missing"][0] ne "x""#, true),
        (r#"any(absent()[*][*] eq "x")"#, false),
        (r#"absent()["z"][0] ne "x""#, true),
    ] {
        assert_eq!(
            scheme
                .parse(expression)
                .unwrap()
                .compile()
                .execute(&context)
                .unwrap(),
            expected,
            "{expression}"
        );
    }
}

#[test]
fn flattened_borrowed_function_results_keep_source_payloads() {
    let payloads = [String::from("first"), String::from("second")];
    let mut builder = SchemeBuilder::new();
    let rows = Type::map(Type::array(Type::Bytes));
    builder.add_field("rows", rows).unwrap();
    add_function(
        &mut builder,
        "echo",
        &[rows],
        rows,
        SimpleFunctionImpl::new(identity),
    );
    let scheme = builder.build();
    let mut context = ExecutionContext::new(&scheme);
    context
        .set_field_value_from_name(
            "rows",
            map(
                Type::array(Type::Bytes),
                [
                    (
                        b"z".as_slice(),
                        array(Type::Bytes, [payloads[1].as_str().into()]),
                    ),
                    (
                        b"a".as_slice(),
                        array(Type::Bytes, [payloads[0].as_str().into()]),
                    ),
                ],
            ),
        )
        .unwrap();
    let result = compile_selection(&scheme, "echo(rows)", vec![FieldIndex::MapEach; 2])
        .execute(&context)
        .unwrap();
    let LhsValue::Array(values) = result else {
        panic!("expected flattened array")
    };
    assert_eq!(values.len(), 2);
    for (value, original) in values.iter().zip(&payloads) {
        let LhsValue::Bytes(Bytes::Borrowed(bytes)) = value else {
            panic!("borrowed function payload was copied")
        };
        assert_eq!(*bytes, original.as_bytes());
        assert_eq!(bytes.as_ptr(), original.as_ptr());
    }
}

type Rows = Vec<BTreeMap<Box<[u8]>, Vec<i64>>>;

struct NativeContext {
    state: NativeContextState,
    rows: Rows,
    missing: Option<Rows>,
    flags: Vec<bool>,
}

impl HasScheme for NativeContext {
    fn scheme(&self) -> &Scheme {
        self.state.scheme()
    }
}

impl EvaluationContext for NativeContext {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        self.state.get_user_data()
    }

    fn get_list_matcher(&self, list: ListRef<'_>) -> &dyn ListMatcher {
        self.state.get_list_matcher(list)
    }
}

wirefilter::wirefilter_fields! {
    impl NativeFields for NativeContext {
        "rows" => { fn(ctx: &NativeContext) -> &Rows { &ctx.rows } },
        "missing" => { fn(ctx: &NativeContext) -> Option<&Rows> { ctx.missing.as_ref() } },
        "flags" => { fn(ctx: &NativeContext) -> &Vec<bool> { &ctx.flags } },
    }
}

fn native_context() -> NativeContext {
    let mut builder = SchemeBuilder::new();
    let rows = Type::array(Type::map(Type::array(Type::Int)));
    builder.add_field("rows", rows).unwrap();
    builder.add_optional_field("missing", rows).unwrap();
    builder.add_field("flags", Type::array(Type::Bool)).unwrap();
    add_function(
        &mut builder,
        "echo_flags",
        &[Type::array(Type::Bool)],
        Type::array(Type::Bool),
        SimpleFunctionImpl::new(identity),
    );
    let scheme = builder.build();
    NativeFields::validate_scheme(&scheme).unwrap();
    NativeContext {
        state: NativeContextState::new(&scheme),
        rows: vec![
            BTreeMap::from([
                (Box::from(b"z".as_slice()), vec![1, 2]),
                (Box::from(b"a".as_slice()), vec![]),
            ]),
            BTreeMap::new(),
            BTreeMap::from([(Box::from(b"a".as_slice()), vec![3])]),
        ],
        missing: None,
        flags: vec![],
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
            _ => panic!("expected custom comparison of a collection"),
        }
    }
}

#[test]
fn native_custom_collection_comparisons_cover_flat_and_nested_selections() {
    use FieldIndex::{ArrayIndex, MapEach, MapKey};
    let context = native_context();
    for (field, indexes, expected) in [
        ("rows", vec![], true.into()),
        ("rows", vec![ArrayIndex(0)], true.into()),
        (
            "rows",
            vec![ArrayIndex(0), MapKey("a".into())],
            false.into(),
        ),
        (
            "rows",
            vec![MapEach],
            array(Type::Bool, [true.into(), false.into(), true.into()]),
        ),
        (
            "rows",
            vec![MapEach, MapEach],
            array(Type::Bool, [false.into(), true.into(), true.into()]),
        ),
        (
            "rows",
            vec![MapEach, MapKey("a".into())],
            array(Type::Bool, [false.into(), true.into()]),
        ),
        (
            "rows",
            vec![MapEach, MapKey("missing".into())],
            array(Type::Bool, []),
        ),
        ("rows", vec![ArrayIndex(1), MapEach], array(Type::Bool, [])),
        ("missing", vec![MapEach], array(Type::Bool, [])),
        ("missing", vec![MapEach, MapEach], array(Type::Bool, [])),
    ] {
        let index = IndexExpr {
            identifier: IdentifierExpr::Field(
                context.scheme().get_field(field).unwrap().to_owned(),
            ),
            indexes: indexes.into_boxed_slice(),
        };
        let compiled = index.compile_with(
            &mut DefaultCompiler::<(), NativeFields>::new(),
            false,
            Nonempty,
        );
        let actual = match compiled {
            CompiledExpr::One(value) => value.execute(&context).into(),
            CompiledExpr::Vec(value) => LhsValue::Array(value.execute(&context).into()),
        };
        assert_eq!(actual, expected, "{field}");
    }
    for field in ["rows", "missing"] {
        for default in [false, true] {
            let index = IndexExpr {
                identifier: IdentifierExpr::Field(
                    context.scheme().get_field(field).unwrap().to_owned(),
                ),
                indexes: Box::new([ArrayIndex(9)]),
            };
            let CompiledExpr::One(compiled) = index.compile_with(
                &mut DefaultCompiler::<(), NativeFields>::new(),
                default,
                Nonempty,
            ) else {
                panic!("expected scalar result")
            };
            assert_eq!(compiled.execute(&context), default);
        }
    }
}

#[test]
fn implicit_boolean_array_iteration_covers_fields_and_function_results() {
    let mut context = native_context();
    for flags in [
        vec![],
        vec![false],
        vec![true, false, true],
        vec![true, true],
    ] {
        for (expression, expected) in [
            ("any(flags)", flags.iter().any(|&value| value)),
            ("all(flags)", flags.iter().all(|&value| value)),
            ("any(echo_flags(flags))", flags.iter().any(|&value| value)),
            ("all(echo_flags(flags))", flags.iter().all(|&value| value)),
        ] {
            context.flags.clone_from(&flags);
            let compiled = context
                .scheme()
                .parse(expression)
                .unwrap()
                .compile_with_compiler(&mut DefaultCompiler::<(), NativeFields>::new());
            assert_eq!(
                compiled.execute(&context).unwrap(),
                expected,
                "{expression}"
            );
        }
    }
}
