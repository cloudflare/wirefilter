use crate::{
    ast::{
        field_expr::{ComparisonExpr, ComparisonOp, ComparisonOpExpr},
        index_expr::IndexExpr,
        simple_expr::{SimpleExpr, UnaryOp},
        Expr,
    },
    filter::{CompiledExpr, CompiledValueExpr},
    functions::{
        ExactSizeChain, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
        FunctionParamError,
    },
    lex::{expect, skip_space, span, take_while, Lex, LexError, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{Array, GetType, LhsValue, RhsValue, Type},
};
use derivative::Derivative;
use serde::Serialize;
use std::iter::once;

/// FunctionCallArgExpr is a function argument. It can be a sub-expression with
/// [`SimpleExpr`], a field with [`IndexExpr`] or a literal with [`Literal`].
#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(tag = "kind", content = "value")]
pub(crate) enum FunctionCallArgExpr<'s> {
    /// IndexExpr is a field that supports the indexing operator.
    IndexExpr(IndexExpr<'s>),
    /// A Literal.
    Literal(RhsValue),
    /// SimpleExpr is a sub-expression which can evaluate to either true/false
    /// or a list of true/false. It compiles to a CompiledExpr and is coerced
    /// into a CompiledValueExpr.
    SimpleExpr(SimpleExpr<'s>),
}

impl<'s> FunctionCallArgExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.uses(field),
            FunctionCallArgExpr::Literal(_) => false,
            FunctionCallArgExpr::SimpleExpr(simple_expr) => simple_expr.uses(field),
        }
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.compile(),
            FunctionCallArgExpr::Literal(literal) => {
                CompiledValueExpr::new(move |_| LhsValue::from(literal.clone()).into())
            }
            // The function argument is an expression compiled as either an
            // CompiledExpr::One or CompiledExpr::Vec.
            // Here we execute the expression to get the actual argument
            // for the function and forward the result in a CompiledValueExpr.
            FunctionCallArgExpr::SimpleExpr(simple_expr) => {
                let compiled_expr = simple_expr.compile();
                match compiled_expr {
                    CompiledExpr::One(expr) => {
                        CompiledValueExpr::new(move |ctx| LhsValue::from(expr.execute(ctx)).into())
                    }
                    CompiledExpr::Vec(expr) => CompiledValueExpr::new(move |ctx| {
                        let result = expr.execute(ctx);
                        LhsValue::Array({
                            let mut arr = Array::new(Type::Bool);
                            for next in result.iter() {
                                arr.push((*next).into()).unwrap();
                            }
                            arr
                        })
                        .into()
                    }),
                }
            }
        }
    }

    pub fn map_each_to(&self) -> Option<Type> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.map_each_to(),
            FunctionCallArgExpr::Literal(_) => None,
            FunctionCallArgExpr::SimpleExpr(_) => None,
        }
    }

    #[allow(dead_code)]
    pub fn simplify(self) -> Self {
        match self {
            FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(ComparisonExpr {
                lhs,
                op: ComparisonOpExpr::IsTrue,
            })) => FunctionCallArgExpr::IndexExpr(lhs),
            _ => self,
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let _initial_input = input;

        macro_rules! c_is_field {
            // characters above F/f in the alphabet mean it can't be a decimal or hex int
            ($c:expr) => {
                (($c.is_ascii_alphanumeric() && !$c.is_ascii_hexdigit()) || $c == '_')
            };
        }

        macro_rules! c_is_field_or_int {
            ($c:expr) => {
                ($c.is_ascii_alphanumeric() || $c == '_')
            };
        }

        // Grammar is ambiguous but lets try to parse the tokens we can be sure of
        // This will provide better error reporting in most cases
        let mut chars = input.chars();
        if let Some(c) = chars.next() {
            // check up to 3 next chars because third char of a hex-string is either ':'
            // or '-'
            let c2 = chars.next();
            let c3 = chars.next();
            if c == '"' {
                return RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input));
            } else if c == '(' || UnaryOp::lex(input).is_ok() {
                return SimpleExpr::lex_with(input, scheme)
                    .map(|(lhs, input)| (FunctionCallArgExpr::SimpleExpr(lhs), input));
            } else if c_is_field!(c)
                || (c_is_field_or_int!(c) && c2.is_some() && c_is_field!(c2.unwrap()))
                || (c_is_field_or_int!(c)
                    && c2.is_some()
                    && c_is_field_or_int!(c2.unwrap())
                    && c3.is_some()
                    && c_is_field!(c3.unwrap()))
            {
                let (lhs, input) = IndexExpr::lex_with(input, scheme)?;
                let lookahead = skip_space(input);
                if ComparisonOp::lex(lookahead).is_ok() {
                    return ComparisonExpr::lex_with_lhs(input, scheme, lhs).map(|(op, input)| {
                        (
                            FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(op)),
                            input,
                        )
                    });
                } else {
                    return Ok((FunctionCallArgExpr::IndexExpr(lhs), input));
                }
            }
        }

        // Fallback to blind parsing next argument
        if let Ok((lhs, input)) = IndexExpr::lex_with(input, scheme) {
            let lookahead = skip_space(input);
            if ComparisonOp::lex(lookahead).is_ok() {
                return ComparisonExpr::lex_with_lhs(input, scheme, lhs).map(|(op, input)| {
                    (
                        FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(op)),
                        input,
                    )
                });
            } else {
                return Ok((FunctionCallArgExpr::IndexExpr(lhs), input));
            }
        }

        RhsValue::lex_with(input, Type::Ip)
            .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Int)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            // try to parse Bytes after Int because digit literals < 255 are wrongly
            // interpreted as Bytes
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            .or_else(|_| Err((LexErrorKind::EOF, _initial_input)))
    }
}

impl<'s> GetType for FunctionCallArgExpr<'s> {
    fn get_type(&self) -> Type {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.get_type(),
            FunctionCallArgExpr::Literal(literal) => literal.get_type(),
            FunctionCallArgExpr::SimpleExpr(simple_expr) => simple_expr.get_type(),
        }
    }
}

impl<'a, 's> From<&'a FunctionCallArgExpr<'s>> for FunctionParam<'a> {
    fn from(arg_expr: &'a FunctionCallArgExpr<'s>) -> Self {
        match arg_expr {
            FunctionCallArgExpr::IndexExpr(expr) => FunctionParam::Variable(expr.get_type()),
            FunctionCallArgExpr::SimpleExpr(expr) => FunctionParam::Variable(expr.get_type()),
            FunctionCallArgExpr::Literal(value) => FunctionParam::Constant(value.into()),
        }
    }
}

#[derive(Derivative, Serialize)]
#[derivative(Debug, PartialEq, Eq, Clone)]
pub(crate) struct FunctionCallExpr<'s> {
    pub name: String,
    #[serde(skip)]
    #[derivative(PartialEq = "ignore")]
    #[allow(clippy::borrowed_box)]
    pub function: &'s Box<dyn FunctionDefinition>,
    #[serde(skip)]
    pub return_type: Type,
    pub args: Vec<FunctionCallArgExpr<'s>>,
    #[serde(skip)]
    pub context: Option<FunctionDefinitionContext>,
}

impl<'s> FunctionCallExpr<'s> {
    #[allow(clippy::borrowed_box)]
    pub fn new(
        name: &str,
        function: &'s Box<dyn FunctionDefinition>,
        args: Vec<FunctionCallArgExpr<'s>>,
        context: Option<FunctionDefinitionContext>,
    ) -> Self {
        let return_type = function.return_type(
            &mut (&args).iter().map(|arg| arg.into()),
            (&context).as_ref(),
        );
        Self {
            name: name.into(),
            function,
            args,
            return_type,
            context,
        }
    }

    pub fn uses(&self, field: Field<'s>) -> bool {
        self.args.iter().any(|arg| arg.uses(field))
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        let ty = self.get_type();
        let Self {
            function,
            args,
            return_type,
            context,
            ..
        } = self;
        let map_each = args.get(0).and_then(|arg| arg.map_each_to());
        let call = function.compile(&mut (&args).iter().map(|arg| arg.into()), context);
        let args = args
            .into_iter()
            .map(FunctionCallArgExpr::compile)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        if map_each.is_some() {
            CompiledValueExpr::new(move |ctx| {
                // Create the output array
                let mut output = Array::new(return_type.clone());
                // Compute value of first argument
                if let Ok(first) = args[0].execute(ctx) {
                    // Apply the function for each element contained
                    // in the first argument and extend output array
                    output.extend(first.into_iter().filter_map(|elem| {
                        call(&mut ExactSizeChain::new(
                            once(Ok(elem)),
                            args[1..].iter().map(|arg| arg.execute(ctx)),
                        ))
                    }));
                }
                Ok(LhsValue::Array(output))
            })
        } else {
            CompiledValueExpr::new(move |ctx| {
                if let Some(value) = call(&mut args.iter().map(|arg| arg.execute(ctx))) {
                    debug_assert!(value.get_type() == ty);
                    Ok(value)
                } else {
                    Err(ty.clone())
                }
            })
        }
    }
}

#[allow(clippy::borrowed_box)]
fn invalid_args_count<'i>(function: &Box<dyn FunctionDefinition>, input: &'i str) -> LexError<'i> {
    let (mandatory, optional) = function.arg_count();
    (
        LexErrorKind::InvalidArgumentsCount {
            expected_min: mandatory,
            expected_max: optional.map(|v| mandatory + v),
        },
        input,
    )
}

impl<'s> GetType for FunctionCallExpr<'s> {
    fn get_type(&self) -> Type {
        let ty = self.return_type.clone();
        if !self.args.is_empty() && self.args[0].map_each_to().is_some() {
            Type::Array(Box::new(ty))
        } else {
            ty
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionCallExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        let (name, mut input) = take_while(input, "function character", |c| {
            c.is_ascii_alphanumeric() || c == '_'
        })?;

        let function = scheme
            .get_function(name)
            .map_err(|err| (LexErrorKind::UnknownFunction(err), initial_input))?;

        input = skip_space(input);

        input = expect(input, "(")?;

        input = skip_space(input);

        let (mandatory_arg_count, optional_arg_count) = function.arg_count();

        let mut args: Vec<FunctionCallArgExpr<'s>> = Vec::new();

        let mut index = 0;

        let mut ctx = function.context();

        while let Some(c) = input.chars().next() {
            if c == ')' {
                break;
            }
            // ',' is expected only if the current argument
            // is not the first one in the list of specified arguments.
            if index != 0 {
                input = expect(input, ",")?;
            }

            input = skip_space(input);

            let (arg, rest) = FunctionCallArgExpr::lex_with(input, scheme)?;

            // Mapping is only accepted for the first argument
            // of a function call for code simplicity
            if arg.map_each_to().is_some() && index != 0 {
                return Err((LexErrorKind::InvalidMapEachAccess, span(input, rest)));
            }

            let next_param = (&arg).into();

            if optional_arg_count.is_some()
                && index >= (mandatory_arg_count + optional_arg_count.unwrap())
            {
                return Err(invalid_args_count(&function, input));
            }

            function
                .check_param(
                    &mut (&args).iter().map(|arg| arg.into()),
                    &next_param,
                    ctx.as_mut(),
                )
                .map_err(|err| match err {
                    FunctionParamError::KindMismatch(err) => (
                        LexErrorKind::InvalidArgumentKind {
                            index,
                            mismatch: err,
                        },
                        span(input, rest),
                    ),
                    FunctionParamError::TypeMismatch(err) => (
                        LexErrorKind::InvalidArgumentType {
                            index,
                            mismatch: err,
                        },
                        span(input, rest),
                    ),
                    FunctionParamError::InvalidConstant(err) => (
                        LexErrorKind::InvalidArgumentValue {
                            index,
                            invalid: err,
                        },
                        span(input, rest),
                    ),
                })?;

            args.push(arg);

            input = skip_space(rest);

            index += 1;
        }

        if args.len() < mandatory_arg_count {
            return Err(invalid_args_count(&function, input));
        }

        input = expect(input, ")")?;

        let function_call = FunctionCallExpr::new(name, function, args, ctx);

        Ok((function_call, input))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{
            field_expr::{ComparisonExpr, ComparisonOpExpr, LhsFieldExpr, OrderingOp},
            logical_expr::{LogicalExpr, LogicalOp},
        },
        functions::{
            FunctionArgKind, FunctionArgKindMismatchError, FunctionArgs, SimpleFunctionDefinition,
            SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam,
        },
        scheme::{FieldIndex, IndexAccessError, UnknownFieldError},
        types::{Array, RhsValues, Type, TypeMismatchError},
    };
    use lazy_static::lazy_static;
    use std::convert::TryFrom;

    fn any_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(v) => Some(LhsValue::Bool(
                Array::try_from(v)
                    .unwrap()
                    .into_iter()
                    .any(|lhs| bool::try_from(lhs).unwrap()),
            )),
            Err(Type::Array(ref arr)) if arr.get_type() == Type::Bool => None,
            _ => unreachable!(),
        }
    }

    fn lower_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        use std::borrow::Cow;

        match args.next()? {
            Ok(LhsValue::Bytes(mut b)) => {
                let mut text: Vec<u8> = b.to_mut().to_vec();
                text.make_ascii_lowercase();
                Some(LhsValue::Bytes(Cow::Owned(text)))
            }
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.headers: Map(Bytes),
                http.host: Bytes,
                http.request.headers.names: Array(Bytes),
                http.request.headers.values: Array(Bytes),
                http.request.headers.is_empty: Array(Bool),
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
            };
            scheme
                .add_function(
                    "any".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Array(Box::new(Type::Bool)),
                        }],
                        opt_params: vec![],
                        return_type: Type::Bool,
                        implementation: SimpleFunctionImpl::new(any_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "echo".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: LhsValue::Int(10),
                            },
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: LhsValue::Int(1),
                            },
                        ],
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(echo_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "lower".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(lower_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "len".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Int,
                        implementation: SimpleFunctionImpl::new(len_function),
                    },
                )
                .unwrap();
            scheme
        };
    }

    #[test]
    fn test_lex_function_call_expr() {
        // test that adjacent single digit int literals are parsed properly
        let expr = assert_ok!(
            FunctionCallExpr::lex_with(r#"echo ( http.host, 1, 2 );"#, &SCHEME),
            FunctionCallExpr {
                name: String::from("echo"),
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with("echo ( http.host );", &SCHEME),
            FunctionCallExpr {
                name: String::from("echo"),
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                    indexes: vec![],
                })],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    }
                ]
            }
        );

        // test that adjacent single digit int literals are parsed properly (without spaces)
        let expr = assert_ok!(
            FunctionCallExpr::lex_with(r#"echo (http.host,1,2);"#, &SCHEME),
            FunctionCallExpr {
                name: String::from("echo"),
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                ],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": 1
                    },
                    {
                        "kind": "Literal",
                        "value": 2
                    }
                ]
            }
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( );", &SCHEME),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(3),
            },
            ");"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.host , http.host );", &SCHEME),
            LexErrorKind::InvalidArgumentKind {
                index: 1,
                mismatch: FunctionArgKindMismatchError {
                    actual: FunctionArgKind::Field,
                    expected: FunctionArgKind::Literal,
                }
            },
            "http.host"
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with("echo ( echo ( http.host ) );", &SCHEME),
            FunctionCallExpr {
                name: String::from("echo"),
                function: SCHEME.get_function("echo").unwrap(),
                args: [FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("echo"),
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(SCHEME.get_field("http.host").unwrap()),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                })]
                .to_vec(),
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": {
                            "name": "echo",
                            "args": [
                                {
                                    "kind": "IndexExpr",
                                    "value": "http.host"
                                }
                            ]
                        }
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with(
                r#"any ( ( http.request.headers.is_empty or http.request.headers.is_empty ) )"#,
                &SCHEME
            ),
            FunctionCallExpr {
                name: String::from("any"),
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Parenthesized(
                    Box::new(LogicalExpr::Combining {
                        op: LogicalOp::Or,
                        items: vec![
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.is_empty").unwrap()
                                    ),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::IsTrue,
                            })),
                            LogicalExpr::Simple(SimpleExpr::Comparison(ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.is_empty").unwrap()
                                    ),
                                    indexes: vec![],
                                },
                                op: ComparisonOpExpr::IsTrue,
                            }))
                        ]
                    })
                ))],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "name": "any",
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "items": [
                                {
                                    "lhs": "http.request.headers.is_empty",
                                    "op": "IsTrue",
                                },
                                {
                                    "lhs": "http.request.headers.is_empty",
                                    "op": "IsTrue",
                                }
                            ],
                            "op": "Or",
                        }
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with("echo ( http.request.headers.names[*] );", &SCHEME),
            FunctionCallExpr {
                name: String::from("echo"),
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                })],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": ["http.request.headers.names", {"kind": "MapEach"}],
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with("echo ( http.headers[*] );", &SCHEME),
            FunctionCallExpr {
                name: String::from("echo"),
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(SCHEME.get_field("http.headers").unwrap()),
                    indexes: vec![FieldIndex::MapEach],
                })],
                return_type: Type::Bytes,
                context: None,
            },
            ";"
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bytes)));

        assert_json!(
            expr,
            {
                "name": "echo",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": ["http.headers", {"kind": "MapEach"}],
                    }
                ]
            }
        );

        assert_ok!(
            FunctionCallArgExpr::lex_with("http.request.headers.names[*] == \"test\"", &SCHEME),
            FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("test".to_owned().into())
                }
            })),
            ""
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with(
                "any(lower(http.request.headers.names[*])[*] contains \"c\")",
                &SCHEME
            ),
            FunctionCallExpr {
                name: "any".into(),
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(
                    ComparisonExpr {
                        lhs: IndexExpr {
                            lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                                name: "lower".into(),
                                function: SCHEME.get_function("lower").unwrap(),
                                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME.get_field("http.request.headers.names").unwrap()
                                    ),
                                    indexes: vec![FieldIndex::MapEach],
                                })],
                                return_type: Type::Bytes,
                                context: None,
                            }),
                            indexes: vec![FieldIndex::MapEach],
                        },
                        op: ComparisonOpExpr::Contains("c".to_string().into(),)
                    }
                ))],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "lhs": [
                                {
                                    "args": [
                                        {
                                            "kind": "IndexExpr",
                                            "value": ["http.request.headers.names", {"kind": "MapEach"}]
                                        }
                                    ],
                                    "name": "lower"
                                },{
                                    "kind": "MapEach"
                                }
                            ],
                            "op": "Contains",
                            "rhs": "c"
                        }
                    }
                ],
                "name": "any"
            }
        );

        let expr = FunctionCallArgExpr::lex_with("lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(http.host)))))))))))))))))))))))))))))))) contains \"c\"", &SCHEME);
        assert!(!expr.is_err());

        let expr = assert_ok!(
            FunctionCallExpr::lex_with("len(http.request.headers.names[*])", &SCHEME),
            FunctionCallExpr {
                name: "len".into(),
                function: SCHEME.get_function("len").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    lhs: LhsFieldExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                })],
                return_type: Type::Int,
                context: None,
            },
            ""
        );

        assert_eq!(expr.args[0].map_each_to(), Some(Type::Bytes));
        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Int)));
    }

    #[test]
    fn test_lex_function_with_unary_expression_as_argument() {
        let expr = assert_ok!(
            FunctionCallExpr::lex_with(
                "any(not(http.request.headers.names[*] in {\"Cookie\" \"Cookies\"}))",
                &SCHEME
            ),
            FunctionCallExpr {
                name: "any".into(),
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(SimpleExpr::Parenthesized(Box::new(LogicalExpr::Simple(
                        SimpleExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                lhs: LhsFieldExpr::Field(
                                    SCHEME.get_field("http.request.headers.names").unwrap()
                                ),
                                indexes: vec![FieldIndex::MapEach],
                            },
                            op: ComparisonOpExpr::OneOf(RhsValues::Bytes(vec![
                                "Cookie".to_owned().into(),
                                "Cookies".to_owned().into(),
                            ])),
                        })
                    ))))
                })],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "name": "any",
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "op": "Not",
                            "arg": {
                                "lhs": [
                                    "http.request.headers.names",
                                    {
                                        "kind": "MapEach"
                                    }
                                ],
                                "op": "OneOf",
                                "rhs": [
                                    "Cookie",
                                    "Cookies"
                                ]
                            }
                        }
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FunctionCallExpr::lex_with(
                "any(!(http.request.headers.names[*] in {\"Cookie\" \"Cookies\"}))",
                &SCHEME
            ),
            FunctionCallExpr {
                name: "any".into(),
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(SimpleExpr::Parenthesized(Box::new(LogicalExpr::Simple(
                        SimpleExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                lhs: LhsFieldExpr::Field(
                                    SCHEME.get_field("http.request.headers.names").unwrap()
                                ),
                                indexes: vec![FieldIndex::MapEach],
                            },
                            op: ComparisonOpExpr::OneOf(RhsValues::Bytes(vec![
                                "Cookie".to_owned().into(),
                                "Cookies".to_owned().into(),
                            ])),
                        })
                    ))))
                })],
                return_type: Type::Bool,
                context: None,
            },
            ""
        );

        assert_json!(
            expr,
            {
                "name": "any",
                "args": [
                    {
                        "kind": "SimpleExpr",
                        "value": {
                            "op": "Not",
                            "arg": {
                                "lhs": [
                                    "http.request.headers.names",
                                    {
                                        "kind": "MapEach"
                                    }
                                ],
                                "op": "OneOf",
                                "rhs": [
                                    "Cookie",
                                    "Cookies"
                                ]
                            }
                        }
                    }
                ]
            }
        );
    }

    #[test]
    fn test_lex_function_call_expr_failure() {
        assert_err!(
            FunctionCallExpr::lex_with("echo ( \"test\" );", &SCHEME),
            LexErrorKind::InvalidArgumentKind {
                index: 0,
                mismatch: FunctionArgKindMismatchError {
                    actual: FunctionArgKind::Literal,
                    expected: FunctionArgKind::Field,
                }
            },
            "\"test\""
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( 10 );", &SCHEME),
            LexErrorKind::InvalidArgumentKind {
                index: 0,
                mismatch: FunctionArgKindMismatchError {
                    actual: FunctionArgKind::Literal,
                    expected: FunctionArgKind::Field,
                }
            },
            "10"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( ip.addr );", &SCHEME),
            LexErrorKind::InvalidArgumentType {
                index: 0,
                mismatch: TypeMismatchError {
                    actual: Type::Ip,
                    expected: Type::Bytes.into(),
                }
            },
            "ip.addr"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.host, 10, 2, \"test\" );", &SCHEME),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(3),
            },
            "\"test\" );"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.test );", &SCHEME),
            LexErrorKind::UnknownField(UnknownFieldError),
            "http.test"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( echo ( http.test ) );", &SCHEME),
            LexErrorKind::UnknownField(UnknownFieldError),
            "http.test"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.host[*] );", &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.request.headers.names[0][*] );", &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.request.headers.names[*][0] );", &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes,
            }),
            "[0]"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.headers[*][\"host\"] );", &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapKey("host".to_string()),
                actual: Type::Bytes,
            }),
            "[\"host\"]"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( http.host, http.headers[*] );", &SCHEME),
            LexErrorKind::InvalidMapEachAccess,
            "http.headers[*]"
        );
    }
}
