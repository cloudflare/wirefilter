use super::{simple_expr::SimpleExpr, Expr};
use crate::{
    filter::{CompiledBoolExpr, CompiledExpr, CompiledVecExpr},
    lex::{skip_space, Lex, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, Type, TypeMismatchError},
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

impl<'s> GetType for CombinedExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            CombinedExpr::Simple(lhs) => lhs.get_type(),
            CombinedExpr::Combining { ref items, .. } => items[0].get_type(),
        }
    }
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

    fn compile(self) -> CompiledExpr<'s> {
        match self {
            CombinedExpr::Simple(op) => op.compile(),
            CombinedExpr::Combining { op, items } => {
                let mut items = items.into_iter();
                let first = items.next().unwrap().compile();
                match first {
                    CompiledExpr::BoolExpr(first) => {
                        let items = items
                            .map(|item| match item.compile() {
                                CompiledExpr::BoolExpr(expr) => expr,
                                CompiledExpr::BoolVecExpr(_) => unreachable!(),
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            CombiningOp::And => {
                                CompiledExpr::BoolExpr(CompiledBoolExpr::new(move |ctx| {
                                    first.execute(ctx) && items.iter().all(|item| item.execute(ctx))
                                }))
                            }
                            CombiningOp::Or => {
                                CompiledExpr::BoolExpr(CompiledBoolExpr::new(move |ctx| {
                                    first.execute(ctx) || items.iter().any(|item| item.execute(ctx))
                                }))
                            }
                            CombiningOp::Xor => {
                                CompiledExpr::BoolExpr(CompiledBoolExpr::new(move |ctx| {
                                    items.iter().fold(first.execute(ctx), |acc, item| {
                                        acc ^ item.execute(ctx)
                                    })
                                }))
                            }
                        }
                    }
                    CompiledExpr::BoolVecExpr(first) => {
                        let items = items
                            .map(|item| match item.compile() {
                                CompiledExpr::BoolExpr(_) => unreachable!(),
                                CompiledExpr::BoolVecExpr(expr) => expr,
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            CombiningOp::And => {
                                CompiledExpr::BoolVecExpr(CompiledVecExpr::new(move |ctx| {
                                    let items = items.iter().map(|item| item.execute(ctx));
                                    let mut output = first.execute(ctx).into_vec();
                                    for values in items {
                                        for (idx, val) in values.iter().enumerate() {
                                            if idx < output.len() {
                                                output[idx] = output[idx] && *val;
                                            }
                                        }
                                        if values.len() < output.len() {
                                            output.truncate(values.len());
                                        }
                                    }
                                    output.into_boxed_slice()
                                }))
                            }
                            CombiningOp::Or => {
                                CompiledExpr::BoolVecExpr(CompiledVecExpr::new(move |ctx| {
                                    let items = items.iter().map(|item| item.execute(ctx));
                                    let mut output = first.execute(ctx).into_vec();
                                    for values in items {
                                        for (idx, val) in values.iter().enumerate() {
                                            if idx < output.len() {
                                                output[idx] = output[idx] || *val;
                                            }
                                        }
                                        if values.len() < output.len() {
                                            output.truncate(values.len());
                                        }
                                    }
                                    output.into_boxed_slice()
                                }))
                            }
                            CombiningOp::Xor => {
                                CompiledExpr::BoolVecExpr(CompiledVecExpr::new(move |ctx| {
                                    let items = items.iter().map(|item| item.execute(ctx));
                                    let mut output = first.execute(ctx).into_vec();
                                    for values in items {
                                        for (idx, val) in values.iter().enumerate() {
                                            if idx < output.len() {
                                                output[idx] ^= *val;
                                            }
                                        }
                                        if values.len() < output.len() {
                                            output.truncate(values.len());
                                        }
                                    }
                                    output.into_boxed_slice()
                                }))
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
#[allow(clippy::cognitive_complexity)]
fn test() {
    use super::field_expr::FieldExpr;
    use crate::{
        execution_context::ExecutionContext,
        lex::complete,
        types::{Array, Type},
    };

    let scheme = &Scheme! {
        t: Bool,
        f: Bool,
        at: Array(Bool),
        af: Array(Bool),
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

    let at_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex_with("at", scheme)).unwrap(),
    ));

    let at_expr = || at_expr.clone();

    let af_expr = CombinedExpr::Simple(SimpleExpr::Field(
        complete(FieldExpr::lex_with("af", scheme)).unwrap(),
    ));

    let af_expr = || af_expr.clone();

    assert_ok!(CombinedExpr::lex_with("at", scheme), at_expr());

    ctx.set_field_value("t", true).unwrap();
    ctx.set_field_value("f", false).unwrap();
    ctx.set_field_value("at", {
        let mut arr = Array::new(Type::Bool);
        arr.push(true.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();
    ctx.set_field_value("af", {
        let mut arr = Array::new(Type::Bool);
        arr.push(false.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("t and t", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![t_expr(), t_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
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

        assert_eq!(expr.execute_one(ctx), false);
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

        assert_eq!(expr.execute_one(ctx), true);
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

        assert_eq!(expr.execute_one(ctx), false);
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

        assert_eq!(expr.execute_one(ctx), true);
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

        assert_eq!(expr.execute_one(ctx), false);
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

        assert_eq!(expr.execute_one(ctx), true);
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

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("at and af", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::And,
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![false, false, true].into_boxed_slice()
        );
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("at or af", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Or,
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![true, false, true].into_boxed_slice()
        );
    }

    {
        let expr = assert_ok!(
            CombinedExpr::lex_with("at xor af", scheme),
            CombinedExpr::Combining {
                op: CombiningOp::Xor,
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![true, false, false].into_boxed_slice()
        );
    }

    {
        assert_err!(
            CombinedExpr::lex_with("t and af", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            CombinedExpr::lex_with("at and f", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            CombinedExpr::lex_with("t or af", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            CombinedExpr::lex_with("at or f", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            CombinedExpr::lex_with("t xor af", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            CombinedExpr::lex_with("at xor f", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }
}
