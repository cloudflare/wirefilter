use super::{combining::CombinedExpr, field::FieldExpr, Expr};
use execution_context::ExecutionContext;
use lex::{expect, Lex, LexResult};
use scheme::{FieldIndex, Scheme};

lex_enum!(UnaryOp {
    "not" | "!" => Not,
});

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum SimpleExpr<'s> {
    Field(FieldExpr<'s>),
    Parenthesized(Box<CombinedExpr<'s>>),
    Unary {
        op: UnaryOp,
        arg: Box<SimpleExpr<'s>>,
    },
}

impl<'s> Expr<'s> for SimpleExpr<'s> {
    fn uses(&self, field: FieldIndex<'s>) -> bool {
        match self {
            SimpleExpr::Field(op) => op.uses(field),
            SimpleExpr::Parenthesized(op) => op.uses(field),
            SimpleExpr::Unary { arg, .. } => arg.uses(field),
        }
    }

    fn lex<'i>(scheme: &'s Scheme, input: &'i str) -> LexResult<'i, Self> {
        Ok(if let Ok(input) = expect(input, "(") {
            let input = input.trim_left();
            let (op, input) = CombinedExpr::lex(scheme, input)?;
            let input = input.trim_left();
            let input = expect(input, ")")?;
            (SimpleExpr::Parenthesized(Box::new(op)), input)
        } else if let Ok((op, input)) = UnaryOp::lex(input) {
            let input = input.trim_left();
            let (arg, input) = SimpleExpr::lex(scheme, input)?;
            (
                SimpleExpr::Unary {
                    op,
                    arg: Box::new(arg),
                },
                input,
            )
        } else {
            let (op, input) = FieldExpr::lex(scheme, input)?;
            (SimpleExpr::Field(op), input)
        })
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
    use types::Type;

    let scheme = &[("x", Type::Bool)]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    let field_expr = || SimpleExpr::Field(complete(FieldExpr::lex(scheme, "x")).unwrap());

    assert_ok!(SimpleExpr::lex(scheme, "x"), field_expr());

    let parenthesized_expr = |expr| SimpleExpr::Parenthesized(Box::new(CombinedExpr::Simple(expr)));

    assert_ok!(
        SimpleExpr::lex(scheme, "(x)"),
        parenthesized_expr(field_expr())
    );

    assert_ok!(
        SimpleExpr::lex(scheme, "((x))"),
        parenthesized_expr(parenthesized_expr(field_expr()))
    );

    let not_expr = |expr| SimpleExpr::Unary {
        op: UnaryOp::Not,
        arg: Box::new(expr),
    };

    assert_ok!(SimpleExpr::lex(scheme, "not x"), not_expr(field_expr()));

    assert_ok!(SimpleExpr::lex(scheme, "!x"), not_expr(field_expr()));

    assert_ok!(
        SimpleExpr::lex(scheme, "!!x"),
        not_expr(not_expr(field_expr()))
    );

    assert_ok!(
        SimpleExpr::lex(scheme, "!(not !x)"),
        not_expr(parenthesized_expr(not_expr(not_expr(field_expr()))))
    );
}
