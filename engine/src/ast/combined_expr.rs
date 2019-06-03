use super::{simple_expr::SimpleExpr, Expr};
use crate::{
    filter::CompiledValueExpr,
    lex::{skip_space, Lex, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, Type, TypeMismatchError},
};
use serde::Serialize;

lex_enum!(#[derive(PartialOrd, Ord)] CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
/// CombinedExpr is an enum with variants [`Simple`], representing
/// either a field, field with an unary operator or a parenthesized
/// expression; and [`Combining`], representing two or more
/// [`CombinedExpr<'s>`] and a logical operator [`CombiningOp`].
///
/// CombinedExpr is used as the root node in the AST, even if the
/// expression does not contain a logical operator.
///
/// However, since the root node of the AST has additional constraints
/// than just CombinedExpr (i.e. comparison of two Array(Bool) is not
/// a valid expression in itself), we enforce these constraints in
/// FilterAst::lex_with.
///
/// ```
/// #[allow(dead_code)]
/// enum FieldIndex {
///     ArrayIndex(u32),
///     MapKey(String),
/// }
/// ```
pub enum CombinedExpr<'s> {
    Simple(SimpleExpr<'s>),
    Combining {
        op: CombiningOp,
        items: Vec<CombinedExpr<'s>>,
    },
}

impl<'s> GetType for CombinedExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            CombinedExpr::Simple(lhs) => lhs.get_type(),
            CombinedExpr::Combining { ref items, .. } => items[0].get_type(),
        }
    }
}

impl<'s> CombinedExpr<'s> {
    /// lex_combining_op returns the CombiningOp at the start of input,
    /// or None, and the remainder of the input.
    fn lex_combining_op(input: &str) -> (Option<CombiningOp>, &str) {
        match CombiningOp::lex(skip_space(input)) {
            Ok((op, input)) => (Some(op), skip_space(input)),
            Err(_) => (None, input),
        }
    }

    /// lex_more_with_precedence lexes the expression on the right hand side of
    /// the operator and returns a complete CombinedExpr or an error with the
    /// input that could not be parsed.
    ///
    /// Since the expression on the right hand side can itself contain further
    /// CombinedExprs lex_more_with_precedence lexes the entire right hand side,
    /// following operator precedence, before checking whether the each side of
    /// the ComparisonExpr is comparable.
    ///
    /// lex_more_with_precedence can be be recursive when we have nested
    /// parenthesized expressions and these are lexed as CombinedExpr
    /// themselves.
    fn lex_more_with_precedence<'i>(
        self,
        scheme: &'s Scheme,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Self> {
        let mut lhs = self;

        while let Some(op) = lookahead.0 {
            // while the next token is a logical operator (CombiningOp) lex the
            // expression on the right hand side of the operator
            let mut rhs = SimpleExpr::lex_with(lookahead.1, scheme)
                .map(|(op, input)| (CombinedExpr::Simple(op), input))?;

            loop {
                // scan until the next token is not a logical operator
                // (CombiningOp) or the operator has a lower precedence.
                lookahead = Self::lex_combining_op(rhs.1);

                if lookahead.0 <= Some(op) {
                    break;
                }

                rhs = rhs
                    .0
                    .lex_more_with_precedence(scheme, lookahead.0, lookahead)?;
            }

            // check that the CombinedExpr is valid by ensuring both the left
            // hand side and right hand side of the operator are comparable.
            // For example, it doesn't make sense to do a logical operator on
            // a Bool and Bytes, or an Array(Bool) with Bool.
            let (lhsty, rhsty) = (lhs.get_type(), rhs.0.get_type());
            match (&lhsty, &rhsty) {
                (Type::Bool, Type::Bool) => {}
                (Type::Array(_), Type::Array(_)) => {}
                _ => {
                    return Err((
                        LexErrorKind::TypeMismatch(TypeMismatchError {
                            expected: lhsty.into(),
                            actual: rhsty,
                        }),
                        lookahead.1,
                    ))
                }
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

    fn compile(self) -> CompiledValueExpr<'s> {
        match self {
            CombinedExpr::Simple(op) => op.compile(),
            CombinedExpr::Combining { op, items } => {
                let items = items
                    .into_iter()
                    .map(Expr::compile)
                    .collect::<Vec<_>>()
                    .into_boxed_slice();

                // need to match on the type and either compile or compile_with
                match op {
                    CombiningOp::And => CompiledValueExpr::new(move |ctx| {
                        Ok(items
                            .iter()
                            .all(|item| match item.execute(ctx) {
                                Ok(LhsValue::Bool(b)) => b,
                                _ => unreachable!(),
                            })
                            .into())
                    }),
                    CombiningOp::Or => CompiledValueExpr::new(move |ctx| {
                        Ok(items
                            .iter()
                            .any(|item| match item.execute(ctx) {
                                Ok(LhsValue::Bool(b)) => b,
                                _ => unreachable!(),
                            })
                            .into())
                    }),
                    CombiningOp::Xor => CompiledValueExpr::new(move |ctx| {
                        Ok(items
                            .iter()
                            .fold(false, |acc, item| match item.execute(ctx) {
                                Ok(LhsValue::Bool(b)) => acc ^ b,
                                _ => unreachable!(),
                            })
                            .into())
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
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

        assert_eq!(expr.execute(ctx), Ok(false.into()));
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
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

        assert_eq!(expr.execute(ctx), Ok(false.into()));
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
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

        assert_eq!(expr.execute(ctx), Ok(false.into()));
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

        assert_eq!(expr.execute(ctx), Ok(true.into()));
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
