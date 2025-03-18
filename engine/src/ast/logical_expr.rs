use super::{
    field_expr::ComparisonExpr,
    parse::FilterParser,
    visitor::{Visitor, VisitorMut},
    Expr,
};
use crate::{
    compiler::Compiler,
    filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr},
    lex::{expect, skip_space, Lex, LexErrorKind, LexResult, LexWith},
    types::{GetType, Type, TypeMismatchError},
};
use serde::Serialize;

lex_enum!(
    /// LogicalOp is an operator for a [`LogicalExpr`]. Its ordering is defined
    /// by the operators' precedences in ascending order.
    #[derive(PartialOrd, Ord)] LogicalOp {
        /// `or` / `||` operator
        "or" | "||" => Or,
        /// `xor` / `^^` operator
        "xor" | "^^" => Xor,
        /// `and` / `&&` operator
        "and" | "&&" => And,
    }
);

lex_enum!(
    /// An operator that takes a single argument
    UnaryOp {
        /// `not` / `!` operator
        "not" | "!" => Not,
    }
);

/// A parenthesized expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(transparent)]
pub struct ParenthesizedExpr<'s> {
    /// The inner expression.
    pub expr: LogicalExpr<'s>,
}

/// LogicalExpr is a either a generic sub-expression
/// or a logical conjunction expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum LogicalExpr<'s> {
    /// Logical conjunction expression
    Combining {
        /// Logical operator
        op: LogicalOp,
        /// List of sub-expressions
        items: Vec<LogicalExpr<'s>>,
    },
    /// A comparison expression.
    Comparison(ComparisonExpr<'s>),
    /// A parenthesized expression.
    Parenthesized(Box<ParenthesizedExpr<'s>>),
    /// A unary expression.
    Unary {
        /// Unary operator.
        op: UnaryOp,
        /// Sub-expression.
        arg: Box<LogicalExpr<'s>>,
    },
}

impl GetType for LogicalExpr<'_> {
    fn get_type(&self) -> Type {
        match &self {
            LogicalExpr::Combining { ref items, .. } => items[0].get_type(),
            LogicalExpr::Comparison(comparison) => comparison.get_type(),
            LogicalExpr::Parenthesized(parenthesized) => parenthesized.expr.get_type(),
            LogicalExpr::Unary { arg, .. } => arg.get_type(),
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

    fn lex_simple_expr<'i>(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        Ok(if let Ok(input) = expect(input, "(") {
            let input = skip_space(input);
            let (expr, input) = LogicalExpr::lex_with(input, parser)?;
            let input = skip_space(input);
            let input = expect(input, ")")?;
            (
                LogicalExpr::Parenthesized(Box::new(ParenthesizedExpr { expr })),
                input,
            )
        } else if let Ok((op, input)) = UnaryOp::lex(input) {
            let input = skip_space(input);
            let (arg, input) = Self::lex_simple_expr(input, parser)?;
            (
                LogicalExpr::Unary {
                    op,
                    arg: Box::new(arg),
                },
                input,
            )
        } else {
            let (op, input) = ComparisonExpr::lex_with(input, parser)?;
            (LogicalExpr::Comparison(op), input)
        })
    }

    fn lex_more_with_precedence<'i>(
        self,
        parser: &FilterParser<'s>,
        min_prec: Option<LogicalOp>,
        mut lookahead: (Option<LogicalOp>, &'i str),
    ) -> LexResult<'i, Self> {
        let mut lhs = self;

        while let Some(op) = lookahead.0 {
            let mut rhs = Self::lex_simple_expr(lookahead.1, parser)?;

            loop {
                lookahead = Self::lex_combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = rhs
                    .0
                    .lex_more_with_precedence(parser, lookahead.0, lookahead)?;
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

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for LogicalExpr<'s> {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (lhs, input) = Self::lex_simple_expr(input, parser)?;
        let lookahead = Self::lex_combining_op(input);
        lhs.lex_more_with_precedence(parser, None, lookahead)
    }
}

impl<'s> Expr<'s> for LogicalExpr<'s> {
    #[inline]
    fn walk<'a, V: Visitor<'s, 'a>>(&'a self, visitor: &mut V) {
        match self {
            LogicalExpr::Comparison(node) => visitor.visit_comparison_expr(node),
            LogicalExpr::Parenthesized(node) => visitor.visit_logical_expr(&node.expr),
            LogicalExpr::Unary { arg, .. } => visitor.visit_logical_expr(arg),
            LogicalExpr::Combining { items, .. } => {
                items
                    .iter()
                    .for_each(|node| visitor.visit_logical_expr(node));
            }
        }
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'s, 'a>>(&'a mut self, visitor: &mut V) {
        match self {
            LogicalExpr::Comparison(node) => visitor.visit_comparison_expr(node),
            LogicalExpr::Parenthesized(node) => visitor.visit_logical_expr(&mut node.expr),
            LogicalExpr::Unary { arg, .. } => visitor.visit_logical_expr(arg),
            LogicalExpr::Combining { items, .. } => {
                items
                    .iter_mut()
                    .for_each(|node| visitor.visit_logical_expr(node));
            }
        }
    }

    fn compile_with_compiler<C: Compiler<'s> + 's>(
        self,
        compiler: &mut C,
    ) -> CompiledExpr<'s, C::U> {
        match self {
            LogicalExpr::Comparison(op) => compiler.compile_comparison_expr(op),
            LogicalExpr::Parenthesized(node) => compiler.compile_logical_expr(node.expr),
            LogicalExpr::Unary {
                op: UnaryOp::Not,
                arg,
            } => {
                let arg = compiler.compile_logical_expr(*arg);
                match arg {
                    CompiledExpr::One(one) => {
                        CompiledExpr::One(CompiledOneExpr::new(move |ctx| !one.execute(ctx)))
                    }
                    CompiledExpr::Vec(vec) => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
                        vec.execute(ctx).iter().map(|item| !item).collect()
                    })),
                }
            }
            LogicalExpr::Combining { op, items } => {
                let items = items.into_iter();
                let mut items = items.map(|item| compiler.compile_logical_expr(item));
                let first = items.next().unwrap();
                match first {
                    CompiledExpr::One(first) => {
                        let items = items
                            .map(|item| match item {
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
                            .map(|item| match item {
                                CompiledExpr::One(_) => unreachable!(),
                                CompiledExpr::Vec(vec) => vec,
                            })
                            .collect::<Vec<_>>()
                            .into_boxed_slice();
                        match op {
                            LogicalOp::And => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
                                let items = items.iter().map(|item| item.execute(ctx));
                                let mut output = first.execute(ctx);
                                for values in items {
                                    output.iter_mut().zip(values.iter()).for_each(
                                        |(left, right)| {
                                            *left = *left && *right;
                                        },
                                    );
                                    if values.len() < output.len() {
                                        output.truncate(values.len());
                                    }
                                }
                                output
                            })),
                            LogicalOp::Or => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
                                let items = items.iter().map(|item| item.execute(ctx));
                                let mut output = first.execute(ctx);
                                for values in items {
                                    output.iter_mut().zip(values.iter()).for_each(
                                        |(left, right)| {
                                            *left = *left || *right;
                                        },
                                    );
                                    if values.len() < output.len() {
                                        output.truncate(values.len());
                                    }
                                }
                                output
                            })),
                            LogicalOp::Xor => CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
                                let items = items.iter().map(|item| item.execute(ctx));
                                let mut output = first.execute(ctx);
                                for values in items {
                                    output.iter_mut().zip(values.iter()).for_each(
                                        |(left, right)| {
                                            *left ^= *right;
                                        },
                                    );
                                    if values.len() < output.len() {
                                        output.truncate(values.len());
                                    }
                                }
                                output
                            })),
                        }
                    }
                }
            }
        }
    }
}

#[test]
#[allow(clippy::bool_assert_comparison)]
#[allow(clippy::cognitive_complexity)]
fn test() {
    use super::field_expr::ComparisonExpr;
    use crate::{
        ast::field_expr::{ComparisonOpExpr, IdentifierExpr},
        ast::index_expr::IndexExpr,
        execution_context::ExecutionContext,
        lex::complete,
        lhs_types::Array,
        scheme::FieldIndex,
        types::Type,
    };

    let scheme = &Scheme! {
        t: Bool,
        f: Bool,
        at: Array(Bool),
        af: Array(Bool),
        aat: Array(Array(Bool)),
    }
    .build();

    let ctx = &mut ExecutionContext::new(scheme);

    let t_expr = LogicalExpr::Comparison(complete(FilterParser::new(scheme).lex_as("t")).unwrap());

    let t_expr = || t_expr.clone();

    let f_expr = LogicalExpr::Comparison(complete(FilterParser::new(scheme).lex_as("f")).unwrap());

    let f_expr = || f_expr.clone();

    assert_ok!(FilterParser::new(scheme).lex_as("t"), t_expr());

    let at_expr =
        LogicalExpr::Comparison(complete(FilterParser::new(scheme).lex_as("at")).unwrap());

    let at_expr = || at_expr.clone();

    let af_expr =
        LogicalExpr::Comparison(complete(FilterParser::new(scheme).lex_as("af")).unwrap());

    let af_expr = || af_expr.clone();

    assert_ok!(FilterParser::new(scheme).lex_as("at"), at_expr());

    ctx.set_field_value(scheme.get_field("t").unwrap(), true)
        .unwrap();
    ctx.set_field_value(scheme.get_field("f").unwrap(), false)
        .unwrap();
    ctx.set_field_value(scheme.get_field("at").unwrap(), {
        Array::from_iter([true, false, true])
    })
    .unwrap();
    ctx.set_field_value(scheme.get_field("af").unwrap(), {
        Array::from_iter([false, false, true])
    })
    .unwrap();

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("t and t"),
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
            FilterParser::new(scheme).lex_as("t and f"),
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
            FilterParser::new(scheme).lex_as("t or f"),
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
            FilterParser::new(scheme).lex_as("f or f"),
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
            FilterParser::new(scheme).lex_as("t xor f"),
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
            FilterParser::new(scheme).lex_as("f xor f"),
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
            FilterParser::new(scheme).lex_as("f xor t"),
            LogicalExpr::Combining {
                op: LogicalOp::Xor,
                items: vec![f_expr(), t_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    assert_ok!(
        FilterParser::new(scheme).lex_as("t or t && t and t or t ^^ t and t || t"),
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
            FilterParser::new(scheme).lex_as("at and af"),
            LogicalExpr::Combining {
                op: LogicalOp::And,
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [false, false, true]);
    }

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("at or af"),
            LogicalExpr::Combining {
                op: LogicalOp::Or,
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [true, false, true]);
    }

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("at xor af"),
            LogicalExpr::Combining {
                op: LogicalOp::Xor,
                items: vec![at_expr(), af_expr()],
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [true, false, false]);
    }

    {
        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("t and af"),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Type::Bool.into()),
            }),
            ""
        );

        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("at and f"),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Type::Bool.into()).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("t or af"),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Type::Bool.into()),
            }),
            ""
        );

        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("at or f"),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Type::Bool.into()).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("t xor af"),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bool.into(),
                actual: Type::Array(Type::Bool.into()),
            }),
            ""
        );

        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("at xor f"),
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Array(Type::Bool.into()).into(),
                actual: Type::Bool,
            }),
            ""
        );
    }

    {
        let expr = assert_ok!(FilterParser::new(scheme).lex_as("t"), t_expr());

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": "t",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_one(ctx), true);
    }

    {
        let expr = assert_ok!(FilterParser::new(scheme).lex_as("at"), at_expr());

        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": "at",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [true, false, true]);
    }

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("at[*]"),
            LogicalExpr::Comparison(ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(scheme.get_field("at").unwrap()),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::IsTrue
            })
        );

        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": ["at", {"kind": "MapEach"}],
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [true, false, true]);
    }

    {
        assert_err!(
            FilterParser::new(scheme).lex_as::<LogicalExpr<'_>>("aat[*]"),
            LexErrorKind::UnsupportedOp {
                lhs_type: Type::Array(Type::Array(Type::Bool.into()).into())
            },
            ""
        );
    }

    let parenthesized_expr =
        |expr| LogicalExpr::Parenthesized(Box::new(ParenthesizedExpr { expr }));

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("((t))"),
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

        assert_eq!(expr.execute_one(ctx), true);
    }

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("((at))"),
            parenthesized_expr(parenthesized_expr(at_expr()))
        );

        assert_json!(
            expr,
            {
                "lhs": "at",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [true, false, true]);
    }

    let not_expr = |expr| LogicalExpr::Unary {
        op: UnaryOp::Not,
        arg: Box::new(expr),
    };

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("not t"),
            not_expr(t_expr())
        );

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

        assert_eq!(expr.execute_one(ctx), false);
    }

    assert_ok!(FilterParser::new(scheme).lex_as("!t"), not_expr(t_expr()));

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("not at"),
            not_expr(at_expr())
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "lhs": "at",
                    "op": "IsTrue"
                }
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [false, true, false]);
    }

    assert_ok!(FilterParser::new(scheme).lex_as("!at"), not_expr(at_expr()));

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("!!t"),
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

        assert_eq!(expr.execute_one(ctx), true);
    }

    assert_ok!(
        FilterParser::new(scheme).lex_as("! (not !t)"),
        not_expr(parenthesized_expr(not_expr(not_expr(t_expr()))))
    );

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("!!at"),
            not_expr(not_expr(at_expr()))
        );

        assert_json!(
            expr,
            {
                "op": "Not",
                "arg": {
                    "op": "Not",
                    "arg": {
                        "lhs": "at",
                        "op": "IsTrue"
                    }
                }
            }
        );

        let expr = expr.compile();

        assert_eq!(expr.execute_vec(ctx), [true, false, true]);
    }

    assert_ok!(
        FilterParser::new(scheme).lex_as("! (not !at)"),
        not_expr(parenthesized_expr(not_expr(not_expr(at_expr()))))
    );

    {
        let expr = assert_ok!(
            FilterParser::new(scheme).lex_as("not t && f"),
            LogicalExpr::Combining {
                op: LogicalOp::And,
                items: vec![not_expr(t_expr()), f_expr()],
            }
        );

        assert_json!(
            expr,
            {
                "op": "And",
                "items": [
                    {
                        "op": "Not",
                        "arg": {
                            "lhs": "t",
                            "op": "IsTrue"
                        }
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
}
