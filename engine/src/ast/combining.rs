use super::{simple::SimpleExpr, Expr};
use execution_context::ExecutionContext;
use lex::{Lex, LexResult};
use scheme::{FieldIndex, Scheme};

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
            let mut rhs = SimpleExpr::lex(scheme, lookahead.1)
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
                        op: op,
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

impl<'s> Expr<'s> for CombinedExpr<'s> {
    fn uses(&self, field: FieldIndex<'s>) -> bool {
        match self {
            CombinedExpr::Simple(op) => op.uses(field),
            CombinedExpr::Combining { items, .. } => items.iter().any(|op| op.uses(field)),
        }
    }

    fn lex<'i>(scheme: &'s Scheme, input: &'i str) -> LexResult<'i, Self> {
        let (lhs, input) = SimpleExpr::lex(scheme, input)?;
        let lookahead = Self::lex_combining_op(input);
        CombinedExpr::Simple(lhs).lex_more_with_precedence(scheme, None, lookahead)
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
    use types::Type;

    let scheme = &[("x", Type::Bool)]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    let field_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex(scheme, "x")).unwrap(),
    ));
    let field_expr = || field_expr.clone();

    assert_ok!(CombinedExpr::lex(scheme, "x"), field_expr());

    assert_ok!(
        CombinedExpr::lex(scheme, "x or x and x and x or x xor x and x or x"),
        CombinedExpr::Combining {
            op: CombiningOp::Or,
            items: vec![
                field_expr(),
                CombinedExpr::Combining {
                    op: CombiningOp::And,
                    items: vec![field_expr(), field_expr(), field_expr()],
                },
                CombinedExpr::Combining {
                    op: CombiningOp::Xor,
                    items: vec![
                        field_expr(),
                        CombinedExpr::Combining {
                            op: CombiningOp::And,
                            items: vec![field_expr(), field_expr()],
                        },
                    ],
                },
                field_expr(),
            ],
        }
    );
}
