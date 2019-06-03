use crate::{
    ast::combined_expr::CombinedExpr,
    ast::index_expr::IndexExpr,
    ast::Expr,
    filter::CompiledValueExpr,
    functions::{FunctionArgKind, FunctionDefinition, FunctionParam, FunctionParamError},
    lex::{expect, skip_space, span, take_while, LexError, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, RhsValue, Type},
};
use derivative::Derivative;
use serde::Serialize;

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(tag = "kind", content = "value")]
pub(crate) enum FunctionCallArgExpr<'s> {
    CombinedExpr(CombinedExpr<'s>),
    IndexExpr(IndexExpr<'s>),
    Literal(RhsValue),
}

impl<'s> FunctionCallArgExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        match self {
            FunctionCallArgExpr::CombinedExpr(combined_expr) => combined_expr.uses(field),
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.uses(field),
            FunctionCallArgExpr::Literal(_) => false,
        }
    }

    pub fn get_kind(&self) -> FunctionArgKind {
        match self {
            FunctionCallArgExpr::CombinedExpr(_) => FunctionArgKind::Field,
            FunctionCallArgExpr::IndexExpr(_) => FunctionArgKind::Field,
            FunctionCallArgExpr::Literal(_) => FunctionArgKind::Literal,
        }
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        match self {
            FunctionCallArgExpr::CombinedExpr(combined_expr) => {
                let compiled_expr = combined_expr.compile();
                CompiledValueExpr::new(move |ctx| compiled_expr.execute(ctx))
            }
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.compile(),
            FunctionCallArgExpr::Literal(literal) => {
                CompiledValueExpr::new(move |_| LhsValue::from(&literal).to_owned().into())
            }
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let _initial_input = input;

        CombinedExpr::lex_with(input, scheme)
            .map(|(lhs, input)| (FunctionCallArgExpr::CombinedExpr(lhs), input))
            .or_else(|_| {
                IndexExpr::lex_with(input, scheme)
                    .map(|(lhs, input)| (FunctionCallArgExpr::IndexExpr(lhs), input))
            })
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Ip)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Int)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            // try to parse Bytes after Int because digit literals < 255 are wrongly interpreted
            // as Bytes
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            .or_else(|_| {
                Err((
                    LexErrorKind::ExpectedName("a valid function argument"),
                    _initial_input,
                ))
            })
    }
}

impl<'s> GetType for FunctionCallArgExpr<'s> {
    fn get_type(&self) -> Type {
        match self {
            FunctionCallArgExpr::CombinedExpr(combined_expr) => combined_expr.get_type(),
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.get_type(),
            FunctionCallArgExpr::Literal(literal) => literal.get_type(),
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
    pub args: Vec<FunctionCallArgExpr<'s>>,
}

impl<'s> FunctionCallExpr<'s> {
    #[allow(clippy::borrowed_box)]
    pub fn new(name: &str, function: &'s Box<dyn FunctionDefinition>) -> Self {
        Self {
            name: name.into(),
            function,
            args: Vec::default(),
        }
    }

    pub fn uses(&self, field: Field<'s>) -> bool {
        self.args.iter().any(|arg| arg.uses(field))
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        let ty = self.get_type();
        let Self { function, args, .. } = self;
        let args = args
            .into_iter()
            .map(FunctionCallArgExpr::compile)
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let (mandatory_arg_count, optional_arg_count) = function.arg_count();
        let max_args = optional_arg_count.map_or_else(|| args.len(), |v| mandatory_arg_count + v);
        CompiledValueExpr::new(move |ctx| {
            match function.execute(&mut args.iter().map(|arg| arg.execute(ctx)).chain(
                (args.len()..max_args).map(|index| Ok(function.default_value(index).unwrap())),
            )) {
                Some(value) => {
                    debug_assert!(value.get_type() == ty);
                    Ok(value)
                }
                None => Err(ty.clone()),
            }
        })
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
        self.function
            .return_type(&mut (&self.args).iter().map(|arg| FunctionParam {
                arg_kind: arg.get_kind(),
                val_type: arg.get_type(),
            }))
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionCallExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        let (name, mut input) = take_while(input, "function character", |c| {
            c.is_ascii_alphanumeric() || c == '_'
        })?;

        input = skip_space(input);

        input = expect(input, "(")?;

        input = skip_space(input);

        let function = scheme
            .get_function(name)
            .map_err(|err| (LexErrorKind::UnknownFunction(err), initial_input))?;

        let (mandatory_arg_count, optional_arg_count) = function.arg_count();

        let mut function_call = FunctionCallExpr::new(name, function);

        let mut params = Vec::new();

        let mut index = 0;

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

            let next_param = FunctionParam {
                arg_kind: arg.get_kind(),
                val_type: arg.get_type(),
            };

            if optional_arg_count.is_some()
                && index >= (mandatory_arg_count + optional_arg_count.unwrap())
            {
                return Err(invalid_args_count(&function, input));
            }

            function
                .check_param(
                    &mut (&function_call.args).iter().map(|arg| FunctionParam {
                        arg_kind: arg.get_kind(),
                        val_type: arg.get_type(),
                    }),
                    &next_param,
                )
                .map_err(|err| match err {
                    FunctionParamError::FunctionArgKindMismatch(err) => (
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
                })?;

            params.push(next_param);

            function_call.args.push(arg);

            input = skip_space(rest);

            index += 1;
        }

        if function_call.args.len() < mandatory_arg_count {
            return Err(invalid_args_count(&function, input));
        }

        input = expect(input, ")")?;

        Ok((function_call, input))
    }
}

#[test]
fn test_function() {
    use super::field_expr::LhsFieldExpr;
    use crate::{
        functions::{
            Function, FunctionArgKindMismatchError, FunctionArgs, FunctionImpl, FunctionOptParam,
        },
        types::{Type, TypeMismatchError},
    };
    use lazy_static::lazy_static;

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.host: Bytes,
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
            };
            scheme
                .add_function(
                    "echo".into(),
                    Function {
                        params: vec![FunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![FunctionOptParam {
                            arg_kind: FunctionArgKind::Literal,
                            default_value: LhsValue::Int(10),
                        }],
                        return_type: Type::Bytes,
                        implementation: FunctionImpl::new(echo_function),
                    },
                )
                .unwrap();
            scheme
        };
    }

    let expr = assert_ok!(
        FunctionCallExpr::lex_with("echo ( http.host );", &SCHEME),
        FunctionCallExpr {
            name: String::from("echo"),
            function: SCHEME.get_function("echo").unwrap(),
            args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                lhs: LhsFieldExpr::Field(SCHEME.get_field_index("http.host").unwrap()),
                indexes: vec![],
            })],
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

    assert_err!(
        FunctionCallExpr::lex_with("echo ( );", &SCHEME),
        LexErrorKind::InvalidArgumentsCount {
            expected_min: 1,
            expected_max: Some(2),
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
                        lhs: LhsFieldExpr::Field(SCHEME.get_field_index("http.host").unwrap()),
                        indexes: vec![],
                    })],
                }),
                indexes: vec![],
            })]
            .to_vec(),
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
        FunctionCallExpr::lex_with("echo ( http.host, 10, \"test\" );", &SCHEME),
        LexErrorKind::InvalidArgumentsCount {
            expected_min: 1,
            expected_max: Some(2),
        },
        "\"test\" );"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( http.test );", &SCHEME),
        LexErrorKind::ExpectedName("a valid function argument"),
        "http.test );"
    );
}
