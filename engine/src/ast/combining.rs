use super::{simple::SimpleExpr, Expr};
use execution_context::ExecutionContext;
use lex::{Lex, LexResult, LexWith};
use scheme::{Field, Scheme};

lex_enum!(#[derive(PartialOrd, Ord)] CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum CombinedExpr<'s> {
    Simple(SimpleExpr<'s>),
    Combining {
        op: CombiningOp,
        items: Vec<CombinedExpr<'s>>,
    },
}

impl<'s> CombinedExpr<'s> {
    fn lex_combining_op(input: &str) -> (Option<CombiningOp>, &str) {
        match CombiningOp::lex(input.trim_left()) {
            Ok((op, input)) => (Some(op), input.trim_left()),
            Err(_) => (None, input),
        }
    }

    fn lex_more_with_precedence<'i>(
        self,
        scheme: &'s Scheme,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Self> {
        let mut lhs = self;

        while let Some(op) = lookahead.0 {
            let mut rhs = SimpleExpr::lex(lookahead.1, scheme)
                .map(|(op, input)| ((CombinedExpr::Simple(op), input)))?;

            loop {
                lookahead = Self::lex_combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = rhs
                    .0
                    .lex_more_with_precedence(scheme, lookahead.0, lookahead)?;
            }

            match lhs {
                CombinedExpr::Combining {
                    op: lhs_op,
                    ref mut items,
                }
                    if lhs_op == op =>
                {
                    items.push(rhs.0);
                }
                _ => {
                    lhs = CombinedExpr::Combining {
                        op,
                        items: vec![lhs, rhs.0],
                    };
                }
            }

            if lookahead.0 < min_prec {
                // pretend we haven't seen an operator if its precedence is
                // outside of our limits
                lookahead = (None, rhs.1);
            }
        }

        Ok((lhs, lookahead.1))
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for CombinedExpr<'s> {
    fn lex(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (lhs, input) = SimpleExpr::lex(input, scheme)?;
        let lookahead = Self::lex_combining_op(input);
        CombinedExpr::Simple(lhs).lex_more_with_precedence(scheme, None, lookahead)
    }
}

impl<'s> Expr<'s> for CombinedExpr<'s> {
    fn uses(&self, field: Field<'s>) -> bool {
        match self {
            CombinedExpr::Simple(op) => op.uses(field),
            CombinedExpr::Combining { items, .. } => items.iter().any(|op| op.uses(field)),
        }
    }

    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        match self {
            CombinedExpr::Simple(op) => op.execute(ctx),
            CombinedExpr::Combining { op, items } => {
                let mut results = items.iter().map(|op| op.execute(ctx));
                match op {
                    CombiningOp::And => results.all(|res| res),
                    CombiningOp::Or => results.any(|res| res),
                    CombiningOp::Xor => results.fold(false, |acc, res| acc ^ res),
                }
            }
        }
    }
}

#[test]
fn test() {
    use super::field::FieldExpr;
    use lex::complete;
    use types::{LhsValue, Type};

    let scheme = &[("t", Type::Bool), ("f", Type::Bool)]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    let ctx = &mut ExecutionContext::new(scheme);

    let t_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex("t", scheme)).unwrap(),
    ));

    let t_expr = || t_expr.clone();

    let f_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex("f", scheme)).unwrap(),
    ));

    let f_expr = || f_expr.clone();

    assert_ok!(CombinedExpr::lex("t", scheme), t_expr());

    ctx.set_field_value("t", LhsValue::Bool(true));
    ctx.set_field_value("f", LhsValue::Bool(false));

    {
        let expr = assert_ok!(
            CombinedExpr::lex("t and t", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![t_expr(), t_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex("t and f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex("t or f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex("f or f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![f_expr(), f_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex("t xor f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex("f xor f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![f_expr(), f_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex("f xor t", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![f_expr(), t_expr()],
            }
        );

        assert_eq!(expr.execute(ctx), true);
    }

    assert_ok!(
        CombinedExpr::lex("t or t && t and t or t ^^ t and t || t", scheme),
        CombinedExpr::Combining {
            op: CombiningOp::Or,
            items: vec![
                t_expr(),
                CombinedExpr::Combining {
                    op: CombiningOp::And,
                    items: vec![t_expr(), t_expr(), t_expr()],
                },
                CombinedExpr::Combining {
                    op: CombiningOp::Xor,
                    items: vec![
                        t_expr(),
                        CombinedExpr::Combining {
                            op: CombiningOp::And,
                            items: vec![t_expr(), t_expr()],
                        },
                    ],
                },
                t_expr(),
            ],
        }
    );
}
