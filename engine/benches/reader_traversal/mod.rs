//! Function-result traversal and native custom-collection comparison.

use criterion::Criterion;
use std::hint::black_box;
use wirefilter::{
    Array, Compare, CompiledExpr, CompiledValueExpr, ContextFamily, DefaultCompiler,
    EvaluationContext, ExecutionContext, FieldIndex, FilterValueExpr, FunctionArgs, HasScheme,
    IdentifierExpr, IndexExpr, LhsValue, ListMatcher, ListRef, Scheme, SchemeBuilder,
    SimpleFunctionArgKind, SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam, Type,
    ValueExpr,
};

fn echo<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    args.next()?.ok()
}

fn own<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    Some(args.next()?.ok()?.into_owned())
}

fn function(ty: Type, implementation: SimpleFunctionImpl) -> SimpleFunctionDefinition {
    SimpleFunctionDefinition {
        params: vec![SimpleFunctionParam {
            arg_kind: SimpleFunctionArgKind::Field,
            val_type: ty,
        }]
        .into_boxed_slice(),
        opt_params: Box::new([]),
        return_type: ty,
        implementation,
    }
}

struct NativeContext {
    scheme: Scheme,
    number: i64,
    numbers: Vec<i64>,
    matrix: Vec<Vec<i64>>,
    cube: Vec<Vec<Vec<i64>>>,
    flags: Vec<bool>,
}

impl HasScheme for NativeContext {
    fn scheme(&self) -> &Scheme {
        &self.scheme
    }
}

impl EvaluationContext for NativeContext {
    type UserData = ();

    fn get_user_data(&self) -> &() {
        &()
    }

    fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
        unreachable!("this benchmark has no lists")
    }
}

wirefilter::wirefilter_fields! {
    impl NativeFields for NativeContext {
        "number" => { fn(ctx: &NativeContext) -> i64 { ctx.number } },
        "numbers" => { fn(ctx: &NativeContext) -> &[i64] { &ctx.numbers } },
        "matrix" => { fn(ctx: &NativeContext) -> &[Vec<i64>] { &ctx.matrix } },
        "cube" => { fn(ctx: &NativeContext) -> &[Vec<Vec<i64>>] { &ctx.cube } },
        "flags" => { fn(ctx: &NativeContext) -> &[bool] { &ctx.flags } },
    }
}

fn context() -> (Scheme, ExecutionContext<'static>, NativeContext) {
    let numbers = Type::array(Type::Int);
    let matrix = Type::array(numbers);
    let cube = Type::array(matrix);
    let flags = Type::array(Type::Bool);
    let mut builder = SchemeBuilder::new();
    for (name, ty) in [
        ("number", Type::Int),
        ("numbers", numbers),
        ("matrix", matrix),
        ("cube", cube),
        ("flags", flags),
    ] {
        builder.add_field(name, ty).unwrap();
        builder
            .add_function(
                format!("echo_{name}"),
                function(ty, SimpleFunctionImpl::new(echo)),
            )
            .unwrap();
        builder
            .add_function(
                format!("own_{name}"),
                function(ty, SimpleFunctionImpl::new(own)),
            )
            .unwrap();
    }
    let scheme = builder.build();
    let native = NativeContext {
        scheme: scheme.clone(),
        number: 63,
        numbers: (0..64).collect(),
        matrix: (0..8).map(|row| (row * 8..row * 8 + 8).collect()).collect(),
        cube: (0..4)
            .map(|plane| {
                (0..4)
                    .map(|row| (plane * 16 + row * 4..plane * 16 + row * 4 + 4).collect())
                    .collect()
            })
            .collect(),
        flags: (0..64).map(|i| i == 63).collect(),
    };
    NativeFields::validate_scheme(&scheme).unwrap();
    let mut context = ExecutionContext::new(&scheme);
    context
        .set_field_value_from_name("number", native.number)
        .unwrap();
    context
        .set_field_value_from_name("numbers", Array::from_iter(native.numbers.iter().copied()))
        .unwrap();
    context
        .set_field_value_from_name(
            "matrix",
            Array::try_from_iter(
                numbers,
                native
                    .matrix
                    .iter()
                    .map(|row| Array::from_iter(row.iter().copied())),
            )
            .unwrap(),
        )
        .unwrap();
    context
        .set_field_value_from_name("flags", Array::from_iter(native.flags.iter().copied()))
        .unwrap();
    (scheme, context, native)
}

fn compile_value_selection(scheme: &Scheme, expression: &str, depth: usize) -> CompiledValueExpr {
    // Parse a complete function call, then benchmark its indexing node directly.
    // Top-level value parsing rejects [*], while function arguments compile this
    // same node and consume its flattened result.
    let ast = scheme.parse_value(expression).unwrap();
    let FilterValueExpr::Index(mut index) = ast.expression().clone() else {
        unreachable!()
    };
    index.indexes = vec![FieldIndex::MapEach; depth].into_boxed_slice();
    index.compile()
}

pub(super) fn bench(c: &mut Criterion) {
    let (scheme, context, native) = context();
    let mut group = c.benchmark_group("reader_traversal");
    for (name, expression) in [
        ("function_scalar", "echo_number(number) eq 63"),
        ("function_index", "echo_numbers(numbers)[63] eq 63"),
        (
            "function_flat_borrowed",
            "any(echo_numbers(numbers)[*] eq 63)",
        ),
        ("function_flat_owned", "any(own_numbers(numbers)[*] eq 63)"),
        (
            "function_nested_borrowed",
            "any(echo_matrix(matrix)[*][*] eq 63)",
        ),
        (
            "function_nested_owned",
            "any(own_matrix(matrix)[*][*] eq 63)",
        ),
        ("implicit_bool_array", "any(flags)"),
        ("implicit_bool_function_borrowed", "any(echo_flags(flags))"),
        ("implicit_bool_function_owned", "any(own_flags(flags))"),
    ] {
        let filter = scheme.parse(expression).unwrap().compile();
        assert!(filter.execute(&context).unwrap(), "{name}");
        group.bench_function(name, |b| {
            b.iter(|| filter.execute(black_box(&context)).unwrap())
        });
    }
    for (name, expression, depth, expected_type, expected_len) in [
        (
            "value_root_borrowed",
            "echo_matrix(matrix)",
            0,
            Type::array(Type::array(Type::Int)),
            8,
        ),
        (
            "value_root_owned",
            "own_matrix(matrix)",
            0,
            Type::array(Type::array(Type::Int)),
            8,
        ),
        (
            "value_flat_borrowed",
            "echo_numbers(numbers)",
            1,
            Type::array(Type::Int),
            64,
        ),
        (
            "value_nested_borrowed",
            "echo_matrix(matrix)",
            2,
            Type::array(Type::Int),
            64,
        ),
        (
            "value_nested_owned",
            "own_matrix(matrix)",
            2,
            Type::array(Type::Int),
            64,
        ),
    ] {
        let value = compile_value_selection(&scheme, expression, depth);
        let result = value.execute(&context).unwrap();
        assert_eq!(wirefilter::GetType::get_type(&result), expected_type);
        let LhsValue::Array(array) = result else {
            unreachable!()
        };
        assert_eq!(array.len(), expected_len);
        group.bench_function(name, |b| {
            b.iter(|| value.execute(black_box(&context)).unwrap())
        });
    }
    let implicit = scheme
        .parse("any(flags)")
        .unwrap()
        .compile_with_compiler(&mut DefaultCompiler::<(), NativeFields>::new());
    assert!(implicit.execute(&native).unwrap());
    group.bench_function("implicit_bool_native", |b| {
        b.iter(|| implicit.execute(black_box(&native)).unwrap())
    });

    for (name, expression) in [
        ("native_scalar", "number eq 63"),
        ("native_array", "any(numbers[*] eq 63)"),
        ("native_nested", "any(matrix[*][*] eq 63)"),
    ] {
        let filter = scheme
            .parse(expression)
            .unwrap()
            .compile_with_compiler(&mut DefaultCompiler::<(), NativeFields>::new());
        assert!(filter.execute(&native).unwrap(), "{name}");
        group.bench_function(name, |b| {
            b.iter(|| filter.execute(black_box(&native)).unwrap())
        });
    }

    for (name, field, indexes) in [
        ("custom_native_root", "matrix", vec![]),
        (
            "custom_native_index",
            "matrix",
            vec![FieldIndex::ArrayIndex(3)],
        ),
        ("custom_native_flat", "matrix", vec![FieldIndex::MapEach]),
        (
            "custom_native_nested",
            "cube",
            vec![FieldIndex::MapEach, FieldIndex::MapEach],
        ),
    ] {
        let expression = IndexExpr {
            identifier: IdentifierExpr::Field(scheme.get_field(field).unwrap().to_owned()),
            indexes: indexes.into_boxed_slice(),
        }
        .compile_with(
            &mut DefaultCompiler::<(), NativeFields>::new(),
            false,
            Nonempty,
        );
        match expression {
            CompiledExpr::One(expression) => {
                assert!(expression.execute(&native));
                group.bench_function(name, |b| b.iter(|| expression.execute(black_box(&native))));
            }
            CompiledExpr::Vec(expression) => {
                assert!(!expression.execute(&native).is_empty());
                group.bench_function(name, |b| b.iter(|| expression.execute(black_box(&native))));
            }
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
        let LhsValue::Array(values) = value else {
            panic!("expected array")
        };
        !values.is_empty()
    }
}
