use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use wirefilter::{
    ComparisonExpr, CompiledExpr, CompiledOneExpr, CompiledVecExpr, Compiler, ExecutionContext,
    Expr, LogicalExpr, LogicalOp, SchemeBuilder, Type,
};

#[derive(Clone, Debug, PartialEq)]
enum Value {
    One(bool),
    Vec(Vec<bool>),
}

struct RecordingCompiler {
    values: VecDeque<Value>,
    calls: Arc<Mutex<Vec<usize>>>,
    child_sizes: Vec<usize>,
}

impl Compiler for RecordingCompiler {
    type U = ();

    fn compile_comparison_expr(&mut self, _: ComparisonExpr) -> CompiledExpr {
        let index = self.child_sizes.len();
        let calls = self.calls.clone();
        match self.values.pop_front().unwrap() {
            Value::One(value) => {
                let closure = move |_: &ExecutionContext<'_>| {
                    calls.lock().unwrap().push(index);
                    value
                };
                self.child_sizes.push(std::mem::size_of_val(&closure));
                CompiledExpr::One(CompiledOneExpr::new(closure))
            }
            Value::Vec(values) => {
                let closure = move |_: &ExecutionContext<'_>| {
                    calls.lock().unwrap().push(index);
                    values.iter().copied().collect()
                };
                self.child_sizes.push(std::mem::size_of_val(&closure));
                CompiledExpr::Vec(CompiledVecExpr::new(closure))
            }
        }
    }
}

fn compile(op: LogicalOp, values: Vec<Value>) -> (CompiledExpr, RecordingCompiler) {
    let ty = match &values[0] {
        Value::One(_) => Type::Bool,
        Value::Vec(_) => Type::Array(Type::Bool.into()),
    };
    let mut builder = SchemeBuilder::new();
    builder.add_field("a", ty).unwrap();
    let scheme = builder.build();
    let child = LogicalExpr::Comparison(ComparisonExpr {
        lhs: wirefilter::IndexExpr {
            identifier: wirefilter::IdentifierExpr::Field(
                scheme.get_field("a").unwrap().to_owned(),
            ),
            indexes: match &values[0] {
                Value::One(_) => Box::new([]),
                Value::Vec(_) => Box::new([wirefilter::FieldIndex::MapEach]),
            },
        },
        op: wirefilter::ComparisonOpExpr::IsTrue,
    });
    let node = LogicalExpr::Combining {
        op,
        items: vec![child; values.len()],
    };
    let mut compiler = RecordingCompiler {
        values: values.into(),
        calls: Arc::default(),
        child_sizes: Vec::new(),
    };
    let compiled = node.compile_with_compiler(&mut compiler);
    assert!(compiler.values.is_empty());
    (compiled, compiler)
}

fn execute(expr: &CompiledExpr) -> Value {
    let scheme = SchemeBuilder::new().build();
    let ctx = ExecutionContext::new(&scheme);
    match expr {
        CompiledExpr::One(expr) => Value::One(expr.execute(&ctx)),
        CompiledExpr::Vec(expr) => Value::Vec(
            wirefilter::Array::from(expr.execute(&ctx))
                .into_iter()
                .map(|value| match value {
                    wirefilter::LhsValue::Bool(value) => value,
                    _ => unreachable!(),
                })
                .collect(),
        ),
    }
}

fn closure_size(expr: CompiledExpr) -> usize {
    match expr {
        CompiledExpr::One(expr) => std::mem::size_of_val(&*expr.into_boxed_closure()),
        CompiledExpr::Vec(expr) => std::mem::size_of_val(&*expr.into_boxed_closure()),
    }
}

#[test]
fn single_item_combinations_forward_the_compiled_child() {
    for op in [LogicalOp::And, LogicalOp::Or, LogicalOp::Xor] {
        for value in [Value::One(true), Value::Vec(vec![true, false])] {
            let (expr, compiler) = compile(op, vec![value.clone()]);
            assert_eq!(execute(&expr), value);
            assert_eq!(*compiler.calls.lock().unwrap(), [0]);
            assert_eq!(compiler.child_sizes.len(), 1);
            assert_eq!(closure_size(expr), compiler.child_sizes[0]);
        }
    }
}

#[test]
fn binary_scalar_combinations_preserve_short_circuiting() {
    for op in [LogicalOp::And, LogicalOp::Or, LogicalOp::Xor] {
        for left in [false, true] {
            for right in [false, true] {
                let expected = match op {
                    LogicalOp::And => left && right,
                    LogicalOp::Or => left || right,
                    LogicalOp::Xor => left ^ right,
                };
                let (expr, compiler) = compile(op, vec![Value::One(left), Value::One(right)]);
                assert_eq!(execute(&expr), Value::One(expected));
                let short_circuit =
                    matches!(op, LogicalOp::And) && !left || matches!(op, LogicalOp::Or) && left;
                assert_eq!(
                    *compiler.calls.lock().unwrap(),
                    if short_circuit { vec![0] } else { vec![0, 1] }
                );
                assert_eq!(compiler.child_sizes.len(), 2);
                assert_eq!(
                    closure_size(expr),
                    2 * std::mem::size_of::<CompiledOneExpr>()
                );
            }
        }
    }
}

#[test]
fn binary_vector_combinations_evaluate_both_children_and_truncate() {
    for op in [LogicalOp::And, LogicalOp::Or, LogicalOp::Xor] {
        for (left, right) in [
            (vec![], vec![true]),
            (vec![true], vec![]),
            (vec![true, false, true], vec![false, true]),
            (vec![false, true], vec![true, true, false]),
        ] {
            let expected = left
                .iter()
                .zip(&right)
                .map(|(&left, &right)| match op {
                    LogicalOp::And => left && right,
                    LogicalOp::Or => left || right,
                    LogicalOp::Xor => left ^ right,
                })
                .collect();
            let (expr, compiler) = compile(op, vec![Value::Vec(left), Value::Vec(right)]);
            assert_eq!(execute(&expr), Value::Vec(expected));
            assert_eq!(*compiler.calls.lock().unwrap(), [0, 1]);
            assert_eq!(compiler.child_sizes.len(), 2);
            assert_eq!(
                closure_size(expr),
                2 * std::mem::size_of::<CompiledVecExpr>()
            );
        }
    }
}
