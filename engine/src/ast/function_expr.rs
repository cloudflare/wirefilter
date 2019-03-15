use super::field_expr::LhsFieldExpr;
use execution_context::ExecutionContext;
use functions::{Function, FunctionArg, FunctionArgKind};
use lex::{expect, skip_space, take, take_while, LexErrorKind, LexResult, LexWith};
use scheme::{Field, Scheme};
use serde::Serialize;
use types::{GetType, LhsValue, RhsValue};

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(tag = "kind", content = "value")]
pub(crate) enum FunctionCallArgExpr<'s> {
    LhsFieldExpr(LhsFieldExpr<'s>),
    Literal(RhsValue),
}

struct SchemeFunctionArg<'s, 'a> {
    scheme: &'s Scheme,
    funcarg: &'a FunctionArg,
    index: usize,
}

impl<'i, 's, 'a> LexWith<'i, SchemeFunctionArg<'s, 'a>> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, scheme_funcarg: SchemeFunctionArg<'s, 'a>) -> LexResult<'i, Self> {
        let initial_input = input;

        match scheme_funcarg.funcarg.arg_kind {
            FunctionArgKind::Field => {
                let (lhs, input) = LhsFieldExpr::lex_with(input, scheme_funcarg.scheme)?;
                if lhs.get_type() != scheme_funcarg.funcarg.val_type {
                    Err((
                        LexErrorKind::InvalidArgumentType {
                            index: scheme_funcarg.index,
                            given: lhs.get_type(),
                            expected: scheme_funcarg.funcarg.val_type,
                        },
                        initial_input,
                    ))
                } else {
                    Ok((FunctionCallArgExpr::LhsFieldExpr(lhs), input))
                }
            }
            FunctionArgKind::Literal => {
                let (rhs_value, input) =
                    RhsValue::lex_with(input, scheme_funcarg.funcarg.val_type)?;
                Ok((FunctionCallArgExpr::Literal(rhs_value), input))
            }
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

    pub fn execute(&self, ctx: &'s ExecutionContext<'s>) -> LhsValue<'_> {
        let mut values: Vec<LhsValue<'_>> = Vec::with_capacity(self.args.len());
        for arg in &self.args {
            values.push(match arg {
                FunctionCallArgExpr::LhsFieldExpr(lhs) => match lhs {
                    LhsFieldExpr::Field(field) => ctx.get_field_value_unchecked(*field),
                    LhsFieldExpr::FunctionCallExpr(call) => call.execute(ctx),
                },
                FunctionCallArgExpr::Literal(literal) => literal.into(),
            })
        }
        self.function.implementation.execute(&values[..])
    }

    pub fn uses(&self, field: Field<'s>) -> bool {
        self.args.iter().any(|arg| match arg {
            FunctionCallArgExpr::LhsFieldExpr(lhs) => lhs.uses(field),
            FunctionCallArgExpr::Literal(_) => false,
        })
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

        let mut function_call = FunctionCallExpr::new(name, function);

        let args_len = function.args.len();

        let opts_len = function.opt_args.len();

        for i in 0..args_len {
            if i == 0 {
                if take(input, 1)?.0 == ")" {
                    break;
                }
            } else {
                input = expect(input, ",").map_err(|(_, input)| {
                    (
                        LexErrorKind::IncompatibleNumberArguments {
                            expected_min: args_len,
                            expected_max: args_len + opts_len,
                        },
                        input,
                    )
                })?;
            }

            input = skip_space(input);

            let arg = FunctionCallArgExpr::lex_with(
                input,
                SchemeFunctionArg {
                    scheme,
                    funcarg: &function.args[i],
                    index: i,
                },
            )?;

            function_call.args.push(arg.0);

            input = skip_space(arg.1);
        }

        if function.args.len() != function_call.args.len() {
            return Err((
                LexErrorKind::IncompatibleNumberArguments {
                    expected_min: args_len,
                    expected_max: args_len + opts_len,
                },
                input,
            ));
        }

        for i in 0..opts_len {
            let opt_arg = &function.opt_args[i];

            input = match take(input, 1)? {
                (",", mut rest) => {
                    let arg_def = FunctionArg {
                        arg_kind: opt_arg.arg_kind.clone(),
                        val_type: opt_arg.value.get_type(),
                    };

                    rest = skip_space(rest);

                    let arg = FunctionCallArgExpr::lex_with(
                        rest,
                        SchemeFunctionArg {
                            scheme,
                            funcarg: &arg_def,
                            index: args_len + i,
                        },
                    )?;

                    function_call.args.push(arg.0);

                    rest = skip_space(arg.1);

                    rest
                }
                _ => {
                    function_call
                        .args
                        .push(FunctionCallArgExpr::Literal(opt_arg.value.clone()));

                    input
                }
            }
        }

        if args_len + opts_len != function_call.args.len() {
            return Err((
                LexErrorKind::IncompatibleNumberArguments {
                    expected_min: args_len,
                    expected_max: args_len + opts_len,
                },
                input,
            ));
        }

        input = expect(input, ")")?;

        Ok((function_call, input))
    }
}

#[test]
fn test_function() {
    use functions::{FunctionImpl, FunctionOptArg};
    use lazy_static::lazy_static;
    use scheme::UnknownFieldError;
    use types::Type;

    fn echo_function<'a>(_: &[LhsValue<'a>]) -> LhsValue<'a> {
        false.into()
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
                        args: vec![FunctionArg {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_args: vec![FunctionOptArg {
                            arg_kind: FunctionArgKind::Literal,
                            value: RhsValue::Int(10),
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
            args: vec![
                FunctionCallArgExpr::LhsFieldExpr(LhsFieldExpr::Field(
                    SCHEME.get_field_index("http.host").unwrap()
                )),
                FunctionCallArgExpr::Literal(RhsValue::Int(10)),
            ],
        },
        ";"
    );

    assert_json!(
        expr,
        {
            "name": "echo",
            "args": [
                {
                    "kind": "LhsFieldExpr",
                    "value": "http.host"
                },
                {
                    "kind": "Literal",
                    "value": 10
                }
            ]
        }
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( );", &SCHEME),
        LexErrorKind::IncompatibleNumberArguments {
            expected_min: 1,
            expected_max: 2
        },
        ");"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( http.host , http.host );", &SCHEME),
        LexErrorKind::ExpectedName("digit"),
        "http.host );"
    );

    let expr = assert_ok!(
        FunctionCallExpr::lex_with("echo ( echo ( http.host ) );", &SCHEME),
        FunctionCallExpr {
            name: String::from("echo"),
            function: SCHEME.get_function("echo").unwrap(),
            args: [
                FunctionCallArgExpr::LhsFieldExpr(LhsFieldExpr::FunctionCallExpr(
                    FunctionCallExpr {
                        name: String::from("echo"),
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::LhsFieldExpr(LhsFieldExpr::Field(
                                SCHEME.get_field_index("http.host").unwrap()
                            )),
                            FunctionCallArgExpr::Literal(RhsValue::Int(10)),
                        ],
                    }
                )),
                FunctionCallArgExpr::Literal(RhsValue::Int(10)),
            ]
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
                    "kind": "LhsFieldExpr",
                    "value": {
                        "name": "echo",
                        "args": [
                            {
                                "kind": "LhsFieldExpr",
                                "value": "http.host"
                            },
                            {
                                "kind": "Literal",
                                "value": 10
                            }
                        ]
                    }
                },
                {
                    "kind": "Literal",
                    "value": 10
                }
            ]
        }
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( \"test\" );", &SCHEME),
        LexErrorKind::ExpectedName("identifier character"),
        "\"test\" );"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( 10 );", &SCHEME),
        LexErrorKind::UnknownField(UnknownFieldError),
        "10"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( ip.addr );", &SCHEME),
        LexErrorKind::InvalidArgumentType {
            index: 0,
            given: Type::Ip,
            expected: Type::Bytes
        },
        "ip.addr );"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( http.host, 10, \"test\" );", &SCHEME),
        LexErrorKind::ExpectedLiteral(")"),
        ", \"test\" );"
    );
}
