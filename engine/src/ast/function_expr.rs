use crate::{
    ast::index_expr::IndexExpr,
    execution_context::ExecutionContext,
    functions::{Function, FunctionArgKind, FunctionArgKindMismatchError, FunctionParam},
    lex::{expect, skip_space, span, take, take_while, LexError, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, RhsValue, Type, TypeMismatchError},
};
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

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
pub(crate) struct FunctionCallExpr<'s> {
    pub name: String,
    #[serde(skip)]
    pub function: &'s Function,
    pub args: Vec<FunctionCallArgExpr<'s>>,
}

impl<'s> FunctionCallExpr<'s> {
    pub fn new(name: &str, function: &'s Function) -> Self {
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
        self.function.implementation.execute(
            self.args.iter().map(|arg| arg.execute(ctx)).chain(
                self.function.opt_params[self.args.len() - self.function.params.len()..]
                    .iter()
                    .map(|opt_arg| opt_arg.default_value.as_ref()),
            ),
        )
    }
}

fn invalid_args_count<'i>(function: &Function, input: &'i str) -> LexError<'i> {
    (
        LexErrorKind::InvalidArgumentsCount {
            expected_min: function.params.len(),
            expected_max: function.params.len() + function.opt_params.len(),
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

        for i in 0..function.params.len() {
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

            if arg.0.get_kind() != function.params[i].arg_kind {
                return Err((
                    LexErrorKind::InvalidArgumentKind {
                        index: i,
                        mismatch: FunctionArgKindMismatchError {
                            actual: arg.0.get_kind(),
                            expected: function.params[i].arg_kind,
                        },
                    },
                    span(input, arg.1),
                ));
            }

            if arg.0.get_type() != function.params[i].val_type {
                return Err((
                    LexErrorKind::InvalidArgumentType {
                        index: i,
                        mismatch: TypeMismatchError {
                            actual: arg.0.get_type(),
                            expected: function.params[i].val_type.clone().into(),
                        },
                    },
                    span(input, arg.1),
                ));
            }

            function_call.args.push(arg.0);

            input = skip_space(arg.1);
        }

        if function_call.args.len() != function.params.len() {
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

            let opt_param = function
                .opt_params
                .get(index)
                .ok_or_else(|| invalid_args_count(&function, input))?;

            let _param = FunctionParam {
                arg_kind: opt_param.arg_kind,
                val_type: opt_param.default_value.get_type(),
            };

            let (arg, rest) = FunctionCallArgExpr::lex_with(input, scheme)?;

            if arg.get_kind() != opt_param.arg_kind {
                return Err((
                    LexErrorKind::InvalidArgumentKind {
                        index: function.params.len() + index,
                        mismatch: FunctionArgKindMismatchError {
                            actual: arg.get_kind(),
                            expected: opt_param.arg_kind,
                        },
                    },
                    span(input, rest),
                ));
            }

            if arg.get_type() != opt_param.default_value.get_type() {
                return Err((
                    LexErrorKind::InvalidArgumentType {
                        index: function.params.len() + index,
                        mismatch: TypeMismatchError {
                            actual: arg.get_type(),
                            expected: opt_param.default_value.get_type().into(),
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
        functions::{FunctionArgs, FunctionImpl, FunctionOptParam},
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
            expected_max: 2
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
            expected_max: 2,
        },
        "\"test\" );"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( http.test );", &SCHEME),
        LexErrorKind::ExpectedName("a valid function argument"),
        "http.test );"
    );
}
