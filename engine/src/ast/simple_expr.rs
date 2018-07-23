use super::{combined_expr::CombinedExpr, field_expr::FieldExpr, Expr};
use execution_context::ExecutionContext;
use lex::{expect, Lex, LexResult, LexWith};
use scheme::{Field, Scheme};

lex_enum!(UnaryOp {
    "not" | "!" => Not,
});

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum SimpleExpr<'s> {
    Field(FieldExpr<'s>),
    Parenthesized(Box<CombinedExpr<'s>>),
    Unary {
        op: UnaryOp,
        arg: Box<SimpleExpr<'s>>,
    },
}

impl<'i, 's> LexWith<'i, &'s Scheme> for SimpleExpr<'s> {
    fn lex(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        Ok(if let Ok(input) = expect(input, "(") {
            let input = input.trim_left();
            let (op, input) = CombinedExpr::lex(input, scheme)?;
            let input = input.trim_left();
            let input = expect(input, ")")?;
            (SimpleExpr::Parenthesized(Box::new(op)), input)
        } else if let Ok((op, input)) = UnaryOp::lex(input) {
            let input = input.trim_left();
            let (arg, input) = SimpleExpr::lex(input, scheme)?;
            (
                SimpleExpr::Unary {
                    op,
                    arg: Box::new(arg),
                },
                input,
            )
        } else {
            let (op, input) = FieldExpr::lex(input, scheme)?;
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

    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        match self {
            SimpleExpr::Field(op) => op.execute(ctx),
            SimpleExpr::Parenthesized(op) => op.execute(ctx),
            SimpleExpr::Unary { op, arg } => match op {
                UnaryOp::Not => !arg.execute(ctx),
            },
        }
    }
}

#[test]
fn test() {
    use lex::complete;
    use types::{LhsValue, Type};

    let scheme = &[("t", Type::Bool)]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    let ctx = &mut ExecutionContext::new(scheme);
    ctx.set_field_value("t", LhsValue::Bool(true));

    let t_expr = SimpleExpr::Field(complete(FieldExpr::lex("t", scheme)).unwrap());
    let t_expr = || t_expr.clone();

    {
        let expr = assert_ok!(SimpleExpr::lex("t", scheme), t_expr());
        assert_eq!(expr.execute(ctx), true);
    }

    let parenthesized_expr = |expr| SimpleExpr::Parenthesized(Box::new(CombinedExpr::Simple(expr)));

    {
        let expr = assert_ok!(
            SimpleExpr::lex("((t))", scheme),
            parenthesized_expr(parenthesized_expr(t_expr()))
        );
        assert_eq!(expr.execute(ctx), true);
    }

    let not_expr = |expr| SimpleExpr::Unary {
        op: UnaryOp::Not,
        arg: Box::new(expr),
    };

    {
        let expr = assert_ok!(SimpleExpr::lex("not t", scheme), not_expr(t_expr()));
        assert_eq!(expr.execute(ctx), false);
    }

    assert_ok!(SimpleExpr::lex("!t", scheme), not_expr(t_expr()));

    {
        let expr = assert_ok!(SimpleExpr::lex("!!t", scheme), not_expr(not_expr(t_expr())));
        assert_eq!(expr.execute(ctx), true);
    }

    assert_ok!(
        SimpleExpr::lex("! (not !t)", scheme),
        not_expr(parenthesized_expr(not_expr(not_expr(t_expr()))))
    );
}
