use super::{simple_expr::SimpleExpr, Expr};
use crate::{
    filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr},
    lex::{skip_space, Lex, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;

lex_enum!(#[derive(PartialOrd, Ord)] LogicalOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub enum LogicalExpr<'s> {
    Simple(SimpleExpr<'s>),
    Combining {
        op: LogicalOp,
        items: Vec<LogicalExpr<'s>>,
    },
}

impl<'s> GetType for LogicalExpr<'s> {
    fn get_type(&self) -> Type {
        match &self {
            LogicalExpr::Simple(lhs) => lhs.get_type(),
            LogicalExpr::Combining { ref items, .. } => items[0].get_type(),
        }
    }
}

impl<'s> LogicalExpr<'s> {
    fn lex_combining_op(input: &str) -> (Option<LogicalOp>, &str) {
        match LogicalOp::lex(skip_space(input)) {
            Ok((op, input)) => (Some(op), skip_space(input)),
            Err(_) => (None, input),
        }
    }

    fn lex_more_with_precedence<'i>(
        self,
        scheme: &'s Scheme,
        min_prec: Option<LogicalOp>,
        mut lookahead: (Option<LogicalOp>, &'i str),
    ) -> LexResult<'i, Self> {
        let mut lhs = self;

        while let Some(op) = lookahead.0 {
            let mut rhs = SimpleExpr::lex_with(lookahead.1, scheme)
                .map(|(op, input)| (LogicalExpr::Simple(op), input))?;

            loop {
                lookahead = Self::lex_combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = rhs
                    .0
                    .lex_more_with_precedence(scheme, lookahead.0, lookahead)?;
            }

            // check that the LogicalExpr is valid by ensuring both the left
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
                LogicalExpr::Combining {
                    op: lhs_op,
                    ref mut items,
                } if lhs_op == op => {
                    items.push(rhs.0);
                }
                _ => {
                    lhs = LogicalExpr::Combining {
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

impl<'i, 's> LexWith<'i, &'s Scheme> for LogicalExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (lhs, input) = SimpleExpr::lex_with(input, scheme)?;
        let lookahead = Self::lex_combining_op(input);
        LogicalExpr::Simple(lhs).lex_more_with_precedence(scheme, None, lookahead)
    }
}

impl<'s> Expr<'s> for LogicalExpr<'s> {
    fn uses(&self, field: Field<'s>) -> bool {
        match self {
            LogicalExpr::Simple(op) => op.uses(field),
            LogicalExpr::Combining { items, .. } => items.iter().any(|op| op.uses(field)),
        }
    }

    fn compile(self) -> CompiledExpr<'s> {
        match self {
            LogicalExpr::Simple(op) => op.compile(),
            LogicalExpr::Combining { op, items } => {
                let mut items = items.into_iter();
                let first = items.next().unwrap().compile();
                match first {
                    CompiledExpr::One(first) => {
                        let items = items
                            .map(|item| match item.compile() {
                                CompiledExpr::One(one) => one,
                                CompiledExpr::Vec(_) => unreachable!(),
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            LogicalOp::And => CompiledExpr::One(CompiledOneExpr::new(move |ctx| {
                                first.execute(ctx) && items.iter().all(|item| item.execute(ctx))
                            })),
                            LogicalOp::Or => CompiledExpr::One(CompiledOneExpr::new(move |ctx| {
                                first.execute(ctx) || items.iter().any(|item| item.execute(ctx))
                            })),
                            LogicalOp::Xor => CompiledExpr::One(CompiledOneExpr::new(move |ctx| {
                                items
                                    .iter()
                                    .fold(first.execute(ctx), |acc, item| acc ^ item.execute(ctx))
                            })),
                        }
                    }
                    CompiledExpr::Vec(first) => {
                        let items = items
                            .map(|item| match item.compile() {
                                CompiledExpr::One(_) => unreachable!(),
                                CompiledExpr::Vec(vec) => vec,
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            LogicalOp::And => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
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
                            })),
                            LogicalOp::Or => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
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
                            })),
                            LogicalOp::Xor => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
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
                            })),
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
    use super::field_expr::ComparisonExpr;
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

    let t_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with("t", scheme)).unwrap(),
    ));

    let t_expr = || t_expr.clone();

    let f_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with("f", scheme)).unwrap(),
    ));

    let f_expr = || f_expr.clone();

    assert_ok!(LogicalExpr::lex_with("t", scheme), t_expr());

    let at_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with("at", scheme)).unwrap(),
    ));

    let at_expr = || at_expr.clone();

    let af_expr = LogicalExpr::Simple(SimpleExpr::Comparison(
        complete(ComparisonExpr::lex_with("af", scheme)).unwrap(),
    ));

    let af_expr = || af_expr.clone();

    assert_ok!(LogicalExpr::lex_with("at", scheme), at_expr());

    ctx.set_field_value(scheme.get_field("t").unwrap(), true)
        .unwrap();
    ctx.set_field_value(scheme.get_field("f").unwrap(), false)
        .unwrap();
    ctx.set_field_value(scheme.get_field("at").unwrap(), {
        let mut arr = Array::new(Type::Bool);
        arr.push(true.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();
    ctx.set_field_value(scheme.get_field("af").unwrap(), {
        let mut arr = Array::new(Type::Bool);
        arr.push(false.into()).unwrap();
        arr.push(false.into()).unwrap();
        arr.push(true.into()).unwrap();
        arr
    })
    .unwrap();

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with("t and t", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::And,
                items: vec![t_expr(), t_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with("t and f", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::And,
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
            LogicalExpr::lex_with("t or f", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Or,
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
            LogicalExpr::lex_with("f or f", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Or,
                items: vec![f_expr(), f_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), false);
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with("t xor f", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Xor,
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
            LogicalExpr::lex_with("f xor f", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Xor,
                items: vec![f_expr(), f_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), false);
    }

    {
        let expr = assert_ok!(
            LogicalExpr::lex_with("f xor t", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Xor,
                items: vec![f_expr(), t_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    assert_ok!(
        LogicalExpr::lex_with("t or t && t and t or t ^^ t and t || t", scheme),
        LogicalExpr::Combining {
            op: LogicalOp::Or,
            items: vec![
                t_expr(),
                LogicalExpr::Combining {
                    op: LogicalOp::And,
                    items: vec![t_expr(), t_expr(), t_expr()],
                },
                LogicalExpr::Combining {
                    op: LogicalOp::Xor,
                    items: vec![
                        t_expr(),
                        LogicalExpr::Combining {
                            op: LogicalOp::And,
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
            LogicalExpr::lex_with("at and af", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::And,
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
            LogicalExpr::lex_with("at or af", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Or,
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
            LogicalExpr::lex_with("at xor af", scheme),
            LogicalExpr::Combining {
                op: LogicalOp::Xor,
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
            LogicalExpr::lex_with("t and af", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            LogicalExpr::lex_with("at and f", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            LogicalExpr::lex_with("t or af", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            LogicalExpr::lex_with("at or f", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            LogicalExpr::lex_with("t xor af", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Box::new(Type::Bool)),
            }),
            ""
        );

        assert_err!(
            LogicalExpr::lex_with("at xor f", scheme),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Box::new(Type::Bool)).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }
}
