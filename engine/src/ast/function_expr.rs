use crate::{
    ast::index_expr::IndexExpr,
    execution_context::ExecutionContext,
    functions::{FunctionArgKind, FunctionArgKindMismatchError, FunctionDefinition, FunctionParam},
    lex::{expect, skip_space, span, take, take_while, LexError, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, RhsValue, Type, TypeMismatchError},
};
use derivative::Derivative;
use serde::Serialize;

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(tag = "kind", content = "value")]
pub(crate) enum FunctionCallArgExpr<'s> {
    IndexExpr(IndexExpr<'s>),
    Literal(RhsValue),
}

impl<'s> FunctionCallArgExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.uses(field),
            FunctionCallArgExpr::Literal(_) => false,
        }
    }

    pub fn execute(&'s self, ctx: &'s ExecutionContext<'s>) -> LhsValue<'s> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.execute(ctx),
            FunctionCallArgExpr::Literal(literal) => literal.into(),
        }
    }

    pub fn get_kind(&self) -> FunctionArgKind {
        match self {
            FunctionCallArgExpr::IndexExpr(_) => FunctionArgKind::Field,
            FunctionCallArgExpr::Literal(_) => FunctionArgKind::Literal,
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let _initial_input = input;

        IndexExpr::lex_with(input, scheme)
            .map(|(lhs, input)| (FunctionCallArgExpr::IndexExpr(lhs), input))
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
    pub function: &'s Box<dyn FunctionDefinition>,
    pub args: Vec<FunctionCallArgExpr<'s>>,
}

impl<'s> FunctionCallExpr<'s> {
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

    pub fn execute(&self, ctx: &'s ExecutionContext<'s>) -> LhsValue<'_> {
        self.function.execute(
            &mut self.args.iter().map(|arg| arg.execute(ctx)).chain(
                (self.args.len()
                    ..self
                        .function
                        .max_arg_count()
                        .unwrap_or_else(|| self.args.len()))
                    .map(|index| self.function.default_value(index).unwrap()),
            ),
        )
    }
}

fn invalid_args_count<'i>(function: &Box<dyn FunctionDefinition>, input: &'i str) -> LexError<'i> {
    (
        LexErrorKind::InvalidArgumentsCount {
            expected_min: function.min_arg_count(),
            expected_max: function.max_arg_count(),
        },
        input,
    )
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

        let mut function_call = FunctionCallExpr::new(name, function);

        for i in 0..function.min_arg_count() {
            if i == 0 {
                if take(input, 1)?.0 == ")" {
                    break;
                }
            } else {
                input = expect(input, ",")
                    .map_err(|(_, input)| invalid_args_count(&function, input))?;
            }

            input = skip_space(input);

            let arg = FunctionCallArgExpr::lex_with(input, scheme)?;

            let next_param = FunctionParam {
                arg_kind: arg.0.get_kind(),
                val_type: arg.0.get_type(),
            };

            let param = function
                .check_param(i, &next_param)
                .ok_or_else(|| invalid_args_count(function, input))?;

            if next_param.arg_kind != param.arg_kind {
                return Err((
                    LexErrorKind::InvalidArgumentKind {
                        index: i,
                        mismatch: FunctionArgKindMismatchError {
                            actual: next_param.arg_kind,
                            expected: param.arg_kind,
                        },
                    },
                    span(input, arg.1),
                ));
            }

            if next_param.val_type != param.val_type {
                return Err((
                    LexErrorKind::InvalidArgumentType {
                        index: i,
                        mismatch: TypeMismatchError {
                            actual: next_param.val_type,
                            expected: param.val_type.into(),
                        },
                    },
                    span(input, arg.1),
                ));
            }

            function_call.args.push(arg.0);

            input = skip_space(arg.1);
        }

        if function_call.args.len() != function.min_arg_count() {
            return Err(invalid_args_count(&function, input));
        }

        let mut index = 0;

        while let Some(c) = input.chars().next() {
            if c == ')' {
                break;
            }
            // ',' is expected only if the current optional argument
            // is not the first one in the list of specified arguments.
            if !function_call.args.is_empty() {
                input = expect(input, ",")?;
            }

            input = skip_space(input);

            let (arg, rest) = FunctionCallArgExpr::lex_with(input, scheme)?;

            let next_param = FunctionParam {
                arg_kind: arg.get_kind(),
                val_type: arg.get_type(),
            };

            let opt_param = function
                .check_param(function.min_arg_count() + index, &next_param)
                .ok_or_else(|| invalid_args_count(function, input))?;

            if next_param.arg_kind != opt_param.arg_kind {
                return Err((
                    LexErrorKind::InvalidArgumentKind {
                        index: function.min_arg_count() + index,
                        mismatch: FunctionArgKindMismatchError {
                            actual: next_param.arg_kind,
                            expected: opt_param.arg_kind,
                        },
                    },
                    span(input, rest),
                ));
            }

            if next_param.val_type != opt_param.val_type {
                return Err((
                    LexErrorKind::InvalidArgumentType {
                        index: function.min_arg_count() + index,
                        mismatch: TypeMismatchError {
                            actual: next_param.val_type,
                            expected: opt_param.val_type.into(),
                        },
                    },
                    span(input, rest),
                ));
            }

            function_call.args.push(arg);

            input = skip_space(rest);

            index += 1;
        }

        input = expect(input, ")")?;

        Ok((function_call, input))
    }
}

#[test]
fn test_function() {
    use super::field_expr::LhsFieldExpr;
    use crate::{
        functions::{Function, FunctionArgs, FunctionImpl, FunctionOptParam},
        types::Type,
    };
    use lazy_static::lazy_static;

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> LhsValue<'a> {
        args.next().unwrap()
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
