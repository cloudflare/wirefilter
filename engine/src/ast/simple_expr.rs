use super::{combined_expr::CombinedExpr, field_expr::FieldExpr, Expr};
use crate::{
    filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr},
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    scheme::{Field, Scheme},
};
use serde::Serialize;

lex_enum!(UnaryOp {
    "not" | "!" => Not,
});

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub enum SimpleExpr<'s> {
    Field(FieldExpr<'s>),
    Parenthesized(Box<CombinedExpr<'s>>),
    Unary {
        op: UnaryOp,
        arg: Box<SimpleExpr<'s>>,
    },
}

impl<'i, 's> LexWith<'i, &'s Scheme> for SimpleExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        Ok(if let Ok(input) = expect(input, "(") {
            let input = skip_space(input);
            let (op, input) = CombinedExpr::lex_with(input, scheme)?;
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
            let (op, input) = FieldExpr::lex_with(input, scheme)?;
            (SimpleExpr::Field(op), input)
        })
    }
}

impl<'s> Expr<'s> for SimpleExpr<'s> {
    fn uses(&self, field: Field<'s>) -> bool {
        match self {
            SimpleExpr::Field(op) => op.uses(field),
            SimpleExpr::Parenthesized(op) => op.uses(field),
            SimpleExpr::Unary { arg, .. } => arg.uses(field),
        }
    }

    fn compile(self) -> CompiledExpr<'s> {
        match self {
            SimpleExpr::Field(op) => op.compile(),
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
fn test() {
    use crate::{execution_context::ExecutionContext, lex::complete};

    let scheme = &Scheme! { t: Bool };

    let ctx = &mut ExecutionContext::new(scheme);
    ctx.set_field_value("t", true).unwrap();

    let t_expr = SimpleExpr::Field(complete(FieldExpr::lex_with("t", scheme)).unwrap());
    let t_expr = || t_expr.clone();

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

    let parenthesized_expr = |expr| SimpleExpr::Parenthesized(Box::new(CombinedExpr::Simple(expr)));

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
}
