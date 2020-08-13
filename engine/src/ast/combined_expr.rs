use super::{simple_expr::SimpleExpr, Expr};
use crate::{
    filter::CompiledExpr,
    lex::{skip_space, Lex, LexResult, LexWith},
    scheme::{Field, Scheme},
};
use serde::Serialize;

lex_enum!(#[derive(PartialOrd, Ord)] CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub enum CombinedExpr<'s> {
    Simple(SimpleExpr<'s>),
    Combining {
        op: CombiningOp,
        items: Vec<CombinedExpr<'s>>,
    },
}

impl<'s> CombinedExpr<'s> {
    fn lex_combining_op(input: &str) -> (Option<CombiningOp>, &str) {
        match CombiningOp::lex(skip_space(input)) {
            Ok((op, input)) => (Some(op), skip_space(input)),
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
            let mut rhs = SimpleExpr::lex_with(lookahead.1, scheme)
                .map(|(op, input)| (CombinedExpr::Simple(op), input))?;

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
                } if lhs_op == op => {
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
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (lhs, input) = SimpleExpr::lex_with(input, scheme)?;
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

    fn compile(self) -> CompiledExpr<'s> {
        match self {
            CombinedExpr::Simple(op) => op.compile(),
            CombinedExpr::Combining { op, items } => {
                let items = items
                    .into_iter()
                    .map(Expr::compile)
                    .collect::<Vec<_>>()
                    .into_boxed_slice();

                match op {
                    CombiningOp::And => {
                        CompiledExpr::new(move |ctx| {
                            let r = items
                                .iter()
                                .map(|item| item.execute(ctx))
                                .all(|r| r.unwrap_or_else(|| false));
                            Some(r)
                        })
                    }
                    CombiningOp::Or => {
                        CompiledExpr::new(move |ctx| {
                            let r = items
                                .iter()
                                .map(|item| item.execute(ctx))
                                .any(|r| r.unwrap_or_else(|| false));
                            Some(r)
                        })
                    }
                    CombiningOp::Xor => CompiledExpr::new(move |ctx| {
                        items
                            .iter()
                            .fold(Some(false), |acc, item| {
                                acc.xor( item.execute(ctx))
                            })
                    }),
                }
            }
        }
    }
}

#[test]
fn test() {
    use super::field_expr::FieldExpr;
    use crate::{execution_context::ExecutionContext, lex::complete};

    let scheme = &Scheme! {
        t: Bool,
        f: Bool,
    };

    let ctx = &mut ExecutionContext::new(scheme);

    let t_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex_with("t", scheme)).unwrap(),
    ));

    let t_expr = || t_expr.clone();

    let f_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex_with("f", scheme)).unwrap(),
    ));

    let f_expr = || f_expr.clone();

    assert_ok!(CombinedExpr::lex_with("t", scheme), t_expr());

    ctx.set_field_value("t", true).unwrap();
    ctx.set_field_value("f", false).unwrap();

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t and t", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![t_expr(), t_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(true));
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t and f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "And",
                "items": [
                    {
                        "lhs": "t",
                        "op": "IsTrue"
                    },
                    {
                        "lhs": "f",
                        "op": "IsTrue"
                    }
                ]
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(false));
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t or f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "Or",
                "items": [
                    {
                        "lhs": "t",
                        "op": "IsTrue"
                    },
                    {
                        "lhs": "f",
                        "op": "IsTrue"
                    }
                ]
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(true));
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("f or f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![f_expr(), f_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(false));
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t xor f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![t_expr(), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "Xor",
                "items": [
                    {
                        "lhs": "t",
                        "op": "IsTrue"
                    },
                    {
                        "lhs": "f",
                        "op": "IsTrue"
                    }
                ]
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(true));
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("f xor f", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![f_expr(), f_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(false));
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("f xor t", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![f_expr(), t_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute(ctx), Some(true));
    }

    assert_ok!(
        CombinedExpr::lex_with("t or t && t and t or t ^^ t and t || t", scheme),
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
