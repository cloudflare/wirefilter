use super::{combined_expr::CombinedExpr, field_expr::FieldExpr, CompiledValueExpr, Expr};
use crate::{
    lex::{expect, skip_space, Lex, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, Type},
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

impl<'s> GetType for SimpleExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            SimpleExpr::Field(op) => op.get_type(),
            SimpleExpr::Parenthesized(op) => op.get_type(),
            SimpleExpr::Unary { arg, .. } => arg.get_type(),
        }
    }
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

    fn compile(self) -> CompiledValueExpr<'s> {
        match self {
            SimpleExpr::Field(op) => op.compile(),
            SimpleExpr::Parenthesized(op) => op.compile(),
            SimpleExpr::Unary {
                op: UnaryOp::Not,
                arg,
            } => {
                let arg = arg.compile();
                CompiledValueExpr::new(move |ctx| match arg.execute(ctx) {
                    Ok(LhsValue::Bool(b)) => Ok(LhsValue::Bool(!b)),
                    _ => unreachable!(),
                })
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
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

        assert_eq!(expr.execute(ctx), Ok(false.into()));
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
    }

    assert_ok!(
        SimpleExpr::lex_with("! (not !t)", scheme),
        not_expr(parenthesized_expr(not_expr(not_expr(t_expr()))))
    );
}
