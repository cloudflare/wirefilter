use super::{field_expr::ComparisonExpr, logical_expr::LogicalExpr, Expr};
use crate::{
    filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr},
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, Type},
};
use serde::Serialize;

lex_enum!(UnaryOp {
    "not" | "!" => Not,
});

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub enum SimpleExpr<'s> {
    Comparison(ComparisonExpr<'s>),
    Parenthesized(Box<LogicalExpr<'s>>),
    Unary {
        op: UnaryOp,
        arg: Box<SimpleExpr<'s>>,
    },
}

impl<'s> GetType for SimpleExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            SimpleExpr::Comparison(op) => op.get_type(),
            SimpleExpr::Parenthesized(op) => op.get_type(),
            SimpleExpr::Unary { arg, .. } => arg.get_type(),
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for SimpleExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        Ok(if let Ok(input) = expect(input, "(") {
            let input = skip_space(input);
            let (op, input) = LogicalExpr::lex_with(input, scheme)?;
            let input = skip_space(input);
            let input = expect(input, ")")?;
            (SimpleExpr::Parenthesized(Box::new(op)), input)
        } else if let Ok((op, input)) = UnaryOp::lex(input) {
            let input = skip_space(input);
            let (arg, input) = SimpleExpr::lex_with(input, scheme)?;
            (
                SimpleExpr::Unary {
                    op,
                    arg: Box::new(arg),
                },
                input,
            )
        } else {
            let (op, input) = ComparisonExpr::lex_with(input, scheme)?;
            (SimpleExpr::Comparison(op), input)
        })
    }
}

impl<'s> Expr<'s> for SimpleExpr<'s> {
    fn uses(&self, field: Field<'s>) -> bool {
        match self {
            SimpleExpr::Comparison(op) => op.uses(field),
            SimpleExpr::Parenthesized(op) => op.uses(field),
            SimpleExpr::Unary { arg, .. } => arg.uses(field),
        }
    }

    fn compile(self) -> CompiledExpr<'s> {
        match self {
            SimpleExpr::Comparison(op) => op.compile(),
            SimpleExpr::Parenthesized(op) => op.compile(),
            SimpleExpr::Unary {
                op: UnaryOp::Not,
                arg,
            } => {
                let arg = arg.compile();
                match arg {
                    CompiledExpr::One(one) => {
                        CompiledExpr::One(CompiledOneExpr::new(move |ctx| !one.execute(ctx)))
                    }
                    CompiledExpr::Vec(vec) => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
                        vec.execute(ctx).iter().map(|item| !item).collect()
                    })),
                }
            }
        }
    }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn test() {
    use crate::{execution_context::ExecutionContext, lex::complete, types::Array};

    let scheme = &Scheme! {
        t: Bool,
        at: Array(Bool),
    };

    let ctx = &mut ExecutionContext::new(scheme);
    ctx.set_field_value(scheme.get_field("t").unwrap(), true)
        .unwrap();
    ctx.set_field_value(scheme.get_field("at").unwrap(), {
        let mut arr = Array::new(Type::Bool);
        arr.push(true.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();

    let t_expr = SimpleExpr::Comparison(complete(ComparisonExpr::lex_with("t", scheme)).unwrap());
    let t_expr = || t_expr.clone();

    let at_expr = SimpleExpr::Comparison(complete(ComparisonExpr::lex_with("at", scheme)).unwrap());
    let at_expr = || at_expr.clone();

    {
        let expr = assert_ok!(SimpleExpr::lex_with("t", scheme), t_expr());

        assert_json!(
            expr,
            {
                "lhs": "t",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    {
        let expr = assert_ok!(SimpleExpr::lex_with("at", scheme), at_expr());

        assert_json!(
            expr,
            {
                "lhs": "at",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![true, false, true].into_boxed_slice()
        );
    }

    let parenthesized_expr = |expr| SimpleExpr::Parenthesized(Box::new(LogicalExpr::Simple(expr)));

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with("((t))", scheme),
            parenthesized_expr(parenthesized_expr(t_expr()))
        );

        assert_json!(
            expr,
            {
                "lhs": "t",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with("((at))", scheme),
            parenthesized_expr(parenthesized_expr(at_expr()))
        );

        assert_json!(
            expr,
            {
                "lhs": "at",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![true, false, true].into_boxed_slice()
        );
    }

    let not_expr = |expr| SimpleExpr::Unary {
        op: UnaryOp::Not,
        arg: Box::new(expr),
    };

    {
        let expr = assert_ok!(SimpleExpr::lex_with("not t", scheme), not_expr(t_expr()));

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "lhs": "t",
                    "op": "IsTrue"
                }
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), false);
    }

    assert_ok!(SimpleExpr::lex_with("!t", scheme), not_expr(t_expr()));

    {
        let expr = assert_ok!(SimpleExpr::lex_with("not at", scheme), not_expr(at_expr()));

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "lhs": "at",
                    "op": "IsTrue"
                }
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![false, true, false].into_boxed_slice()
        );
    }

    assert_ok!(SimpleExpr::lex_with("!at", scheme), not_expr(at_expr()));

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with("!!t", scheme),
            not_expr(not_expr(t_expr()))
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "op": "Not",
                    "arg": {
                        "lhs": "t",
                        "op": "IsTrue"
                    }
                }
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    assert_ok!(
        SimpleExpr::lex_with("! (not !t)", scheme),
        not_expr(parenthesized_expr(not_expr(not_expr(t_expr()))))
    );

    {
        let expr = assert_ok!(
            SimpleExpr::lex_with("!!at", scheme),
            not_expr(not_expr(at_expr()))
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "op": "Not",
                    "arg": {
                        "lhs": "at",
                        "op": "IsTrue"
                    }
                }
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![true, false, true].into_boxed_slice()
        );
    }

    assert_ok!(
        SimpleExpr::lex_with("! (not !at)", scheme),
        not_expr(parenthesized_expr(not_expr(not_expr(at_expr()))))
    );
}
