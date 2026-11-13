//! Compare built-in and downstream field getters using the same LhsValue reader.
//!
//! `execution_context` uses the default family and internal field accessor.
//! `public_getter` uses a downstream getter and the public field accessor, which
//! checks the scheme on each read.

use criterion::{BenchmarkId, Criterion};
use std::hint::black_box;
use wirefilter::{
    Array, Compare, CompiledExpr, ContextFamily, DefaultCompiler, ExecutionContext, Field,
    FieldBindingError, FieldConsumer, FieldGetter, FieldIndex, FunctionArgs, IdentifierExpr,
    IndexExpr, LhsValue, LhsValueProvider, Map, Scheme, SchemeBuilder, SimpleFunctionArgKind,
    SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam, Type, TypeMismatchError,
};

struct LhsFields;

impl ContextFamily for LhsFields {
    type Context<'data> = ExecutionContext<'data>;
    type UserData = ();

    fn bind<B: FieldConsumer<Self>>(
        field: Field,
        consumer: B,
    ) -> Result<B::Output, FieldBindingError> {
        consumer.consume(field, LhsGetter)
    }
}

struct LhsGetter;

impl FieldGetter<LhsFields> for LhsGetter {
    type Provider = LhsValueProvider;

    fn get<'ctx, 'data: 'ctx>(
        &self,
        context: &'ctx ExecutionContext<'data>,
        field: &Field,
    ) -> Option<&'ctx LhsValue<'ctx>> {
        context.get_field_value(field.as_ref())
    }
}

fn count<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let len = match args.next()?.ok()? {
        LhsValue::Array(values) => values.len(),
        LhsValue::Map(values) => values.len(),
        _ => unreachable!(),
    };
    Some(LhsValue::Int(i64::try_from(len).unwrap()))
}

fn has_header<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let LhsValue::Bytes(name) = args.next()?.ok()? else {
        unreachable!()
    };
    let LhsValue::Map(headers) = args.next()?.ok()? else {
        unreachable!()
    };
    Some(LhsValue::Bool(headers.get(name.as_ref()).is_some()))
}

fn function(
    params: &[Type],
    return_type: Type,
    implementation: SimpleFunctionImpl,
) -> SimpleFunctionDefinition {
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
    }
}

fn context() -> (Scheme, ExecutionContext<'static>) {
    let strings = Type::array(Type::Bytes);
    let headers = Type::map(strings);
    let mut builder = SchemeBuilder::new();
    for (name, ty) in [
        ("flag", Type::Bool),
        ("port", Type::Int),
        ("ip", Type::Ip),
        ("text", Type::Bytes),
        ("numbers", Type::array(Type::Int)),
        ("matrix", Type::array(Type::array(Type::Int))),
        ("names", strings),
        ("headers", headers),
    ] {
        builder.add_field(name, ty).unwrap();
    }
    for (name, params, output, implementation) in [
        (
            "lower",
            vec![Type::Bytes],
            Type::Bytes,
            SimpleFunctionImpl::new(super::lowercase),
        ),
        (
            "count_values",
            vec![strings],
            Type::Int,
            SimpleFunctionImpl::new(count),
        ),
        (
            "count_headers",
            vec![headers],
            Type::Int,
            SimpleFunctionImpl::new(count),
        ),
        (
            "has_header",
            vec![Type::Bytes, headers],
            Type::Bool,
            SimpleFunctionImpl::new(has_header),
        ),
    ] {
        builder
            .add_function(name, function(&params, output, implementation))
            .unwrap();
    }
    let scheme = builder.build();
    let mut context = ExecutionContext::new(&scheme);
    for (name, value) in [
        ("flag", LhsValue::Bool(true)),
        ("port", LhsValue::Int(443)),
        ("ip", LhsValue::Ip("192.0.2.1".parse().unwrap())),
        ("text", LhsValue::from("example-value-0123456789")),
        (
            "numbers",
            Array::try_from_iter(Type::Int, 0..64_i64).unwrap().into(),
        ),
        (
            "matrix",
            Array::try_from_iter(
                Type::array(Type::Int),
                (0..8).map(|row| Array::try_from_iter(Type::Int, row * 8..row * 8 + 8).unwrap()),
            )
            .unwrap()
            .into(),
        ),
        (
            "names",
            Array::try_from_iter(
                Type::Bytes,
                (0..64).map(|index| LhsValue::from(format!("x-test-{index}").into_bytes())),
            )
            .unwrap()
            .into(),
        ),
        (
            "headers",
            Map::try_from_iter(
                strings,
                (0..64).map(|index| {
                    Ok::<_, TypeMismatchError>((
                        format!("x-test-{index}").into_bytes().into_boxed_slice(),
                        Array::try_from_iter(Type::Bytes, ["clean", "also-clean"]).unwrap(),
                    ))
                }),
            )
            .unwrap()
            .into(),
        ),
    ] {
        context
            .set_field_value(scheme.get_field(name).unwrap(), value)
            .unwrap();
    }
    (scheme, context)
}

pub(super) fn bench(c: &mut Criterion) {
    let (scheme, context) = context();
    let mut group = c.benchmark_group("lhs_value_reader");
    for (name, expression) in [
        ("bool", "flag"),
        ("integer_ordering", "port > 80"),
        ("ip_membership", "ip in {192.0.2.0/24}"),
        ("bytes_equal", r#"text eq "example-value-0123456789""#),
        ("bytes_contains", r#"text contains "value""#),
        ("array_index", "numbers[63] eq 63"),
        ("array_missing", "numbers[100] eq 63"),
        ("array_each", "any(numbers[*] eq 63)"),
        ("nested_each", "any(matrix[*][*] eq 63)"),
        ("map_index", r#"headers["x-test-0"][0] eq "clean""#),
        ("map_missing", r#"headers["missing"][0] eq "clean""#),
        ("map_each", r#"any(headers[*][*] eq "missing")"#),
        (
            "selected_function",
            r#"any(lower(headers["x-test-0"][*])[*] eq "clean")"#,
        ),
        ("array_function", "count_values(names) eq 64"),
        ("map_function", "count_headers(headers) eq 64"),
        ("map_each_function", "all(count_values(headers[*])[*] eq 2)"),
        ("mapped_extra_map", "all(has_header(names[*], headers))"),
    ] {
        let ast = scheme.parse(expression).unwrap();
        let execution_context = ast.clone().compile();
        let public_getter = ast.compile_with_compiler(&mut DefaultCompiler::<(), LhsFields>::new());
        let expected = execution_context.execute(&context).unwrap();
        assert_eq!(expected, public_getter.execute(&context).unwrap(), "{name}");
        group.bench_function(BenchmarkId::new("execution_context", name), |b| {
            b.iter(|| execution_context.execute(black_box(&context)).unwrap())
        });
        group.bench_function(BenchmarkId::new("public_getter", name), |b| {
            b.iter(|| public_getter.execute(black_box(&context)).unwrap())
        });
    }
    for (name, field, indexes) in [
        ("custom_map", "headers", vec![]),
        (
            "custom_selected_array",
            "headers",
            vec![FieldIndex::MapKey("x-test-0".into())],
        ),
        ("custom_each_array", "matrix", vec![FieldIndex::MapEach]),
    ] {
        let index = IndexExpr {
            identifier: IdentifierExpr::Field(scheme.get_field(field).unwrap().to_owned()),
            indexes: indexes.into_boxed_slice(),
        };
        let execution_context =
            index
                .clone()
                .compile_with(&mut DefaultCompiler::<()>::new(), false, Nonempty);
        let public_getter = index.compile_with(
            &mut DefaultCompiler::<(), LhsFields>::new(),
            false,
            Nonempty,
        );
        match (execution_context, public_getter) {
            (CompiledExpr::One(execution_context), CompiledExpr::One(public_getter)) => {
                let expected = execution_context.execute(&context);
                assert_eq!(expected, public_getter.execute(&context));
                group.bench_function(BenchmarkId::new("execution_context", name), |b| {
                    b.iter(|| execution_context.execute(black_box(&context)))
                });
                group.bench_function(BenchmarkId::new("public_getter", name), |b| {
                    b.iter(|| public_getter.execute(black_box(&context)))
                });
            }
            (CompiledExpr::Vec(execution_context), CompiledExpr::Vec(public_getter)) => {
                let expected = execution_context.execute(&context);
                assert_eq!(expected, public_getter.execute(&context));
                group.bench_function(BenchmarkId::new("execution_context", name), |b| {
                    b.iter(|| execution_context.execute(black_box(&context)))
                });
                group.bench_function(BenchmarkId::new("public_getter", name), |b| {
                    b.iter(|| public_getter.execute(black_box(&context)))
                });
            }
            _ => panic!("comparison cardinality changed"),
        }
    }
    group.finish();
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
            _ => panic!("custom comparator expects a collection"),
        }
    }
}
