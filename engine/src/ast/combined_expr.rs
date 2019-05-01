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
                        CompiledExpr::new(move |ctx| items.iter().all(|item| item.execute(ctx)))
                    }
                    CombiningOp::Or => {
                        CompiledExpr::new(move |ctx| items.iter().any(|item| item.execute(ctx)))
                    }
                    CombiningOp::Xor => CompiledExpr::new(move |ctx| {
                        items
                            .iter()
                            .fold(false, |acc, item| acc ^ item.execute(ctx))
                    }),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast::field_expr::FieldExpr, execution_context::ExecutionContext, lex::complete};
    use lazy_static::lazy_static;

    lazy_static! {
        static ref SCHEME: Scheme = Scheme! {
            t: Bool,
            f: Bool,
        };
        static ref T_EXPR: CombinedExpr<'static> = CombinedExpr::Simple(SimpleExpr::Field(
            complete(FieldExpr::lex_with("t", &SCHEME)).unwrap(),
        ));
        static ref F_EXPR: CombinedExpr<'static> = CombinedExpr::Simple(SimpleExpr::Field(
            complete(FieldExpr::lex_with("f", &SCHEME)).unwrap(),
        ));
    }

    #[test]
    fn test_true_and_true() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t and t", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![T_EXPR.clone(), T_EXPR.clone()],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_true_and_false() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t and f", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![T_EXPR.clone(), F_EXPR.clone()],
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
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_true_or_false() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t or f", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![T_EXPR.clone(), F_EXPR.clone()],
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
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_false_or_false() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("f or f", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![F_EXPR.clone(), F_EXPR.clone()],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_true_xor_false() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t xor f", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![T_EXPR.clone(), F_EXPR.clone()],
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
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_false_xor_false() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("f xor f", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![F_EXPR.clone(), F_EXPR.clone()],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_false_xor_true() {
        let expr = assert_ok!(
            CombinedExpr::lex_with("f xor t", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![F_EXPR.clone(), T_EXPR.clone()],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("t", true).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("f", false).unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_complex_ast() {
        assert_ok!(
            CombinedExpr::lex_with("t or t && t and t or t ^^ t and t || t", &SCHEME),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![
                    T_EXPR.clone(),
                    CombinedExpr::Combining {
                        op: CombiningOp::And,
                        items: vec![T_EXPR.clone(), T_EXPR.clone(), T_EXPR.clone()],
                    },
                    CombinedExpr::Combining {
                        op: CombiningOp::Xor,
                        items: vec![
                            T_EXPR.clone(),
                            CombinedExpr::Combining {
                                op: CombiningOp::And,
                                items: vec![T_EXPR.clone(), T_EXPR.clone()],
                            },
                        ],
                    },
                    T_EXPR.clone(),
                ],
            }
        );
    }
}
