use super::field_expr::LhsFieldExpr;
use crate::{
    execution_context::ExecutionContext,
    functions::{Function, FunctionArgKind, FunctionParam},
    lex::{expect, skip_space, span, take, take_while, LexError, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{GetType, LhsValue, RhsValue, TypeMismatchError},
};
use serde::Serialize;

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(tag = "kind", content = "value")]
pub(crate) enum FunctionCallArgExpr<'s> {
    LhsFieldExpr(LhsFieldExpr<'s>),
    Literal(RhsValue),
}

impl<'s> FunctionCallArgExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        match self {
            FunctionCallArgExpr::LhsFieldExpr(lhs) => lhs.uses(field),
            FunctionCallArgExpr::Literal(_) => false,
        }
    }

    pub fn execute(&'s self, ctx: &'s ExecutionContext<'s>) -> LhsValue<'s> {
        match self {
            FunctionCallArgExpr::LhsFieldExpr(lhs) => match lhs {
                LhsFieldExpr::Field(field) => ctx.get_field_value_unchecked(*field),
                LhsFieldExpr::FunctionCallExpr(call) => call.execute(ctx),
            },
            FunctionCallArgExpr::Literal(literal) => literal.into(),
        }
    }
}

struct SchemeFunctionParam<'s, 'a> {
    scheme: &'s Scheme,
    param: &'a FunctionParam,
    index: usize,
}

impl<'i, 's, 'a> LexWith<'i, SchemeFunctionParam<'s, 'a>> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, ctx: SchemeFunctionParam<'s, 'a>) -> LexResult<'i, Self> {
        let initial_input = input;

        match ctx.param.arg_kind {
            FunctionArgKind::Field => {
                let (lhs, input) = LhsFieldExpr::lex_with(input, ctx.scheme)?;
                if lhs.get_type() != ctx.param.val_type {
                    Err((
                        LexErrorKind::InvalidArgumentType {
                            index: ctx.index,
                            mismatch: TypeMismatchError {
                                actual: lhs.get_type(),
                                expected: ctx.param.val_type,
                            },
                        },
                        span(initial_input, input),
                    ))
                } else {
                    Ok((FunctionCallArgExpr::LhsFieldExpr(lhs), input))
                }
            }
            FunctionArgKind::Literal => {
                let (rhs_value, input) = RhsValue::lex_with(input, ctx.param.val_type)?;
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

            let arg = FunctionCallArgExpr::lex_with(
                input,
                SchemeFunctionParam {
                    scheme,
                    param: &function.params[i],
                    index: i,
                },
            )?;

            function_call.args.push(arg.0);

            input = skip_space(arg.1);
        }

        if function_call.args.len() != function.params.len() {
            return Err(invalid_args_count(&function, input));
        }

        let mut index = 0;

        while let Some(',') = input.chars().next() {
            input = skip_space(take(input, 1)?.1);

            let opt_param = function
                .opt_params
                .get(index)
                .ok_or_else(|| invalid_args_count(&function, input))?;

            let param = FunctionParam {
                arg_kind: opt_param.arg_kind.clone(),
                val_type: opt_param.default_value.get_type(),
            };

            let (arg, rest) = FunctionCallArgExpr::lex_with(
                input,
                SchemeFunctionParam {
                    scheme,
                    param: &param,
                    index: function.params.len() + index,
                },
            )?;

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
    use crate::{
        functions::{FunctionArgs, FunctionImpl, FunctionOptParam},
        scheme::UnknownFieldError,
        types::Type,
    };
    use lazy_static::lazy_static;

    fn echo_function<'a>(_: FunctionArgs<'_, 'a>) -> LhsValue<'a> {
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
            args: vec![FunctionCallArgExpr::LhsFieldExpr(LhsFieldExpr::Field(
                SCHEME.get_field_index("http.host").unwrap()
            ))],
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
        LexErrorKind::ExpectedName("digit"),
        "http.host );"
    );

    let expr = assert_ok!(
        FunctionCallExpr::lex_with("echo ( echo ( http.host ) );", &SCHEME),
        FunctionCallExpr {
            name: String::from("echo"),
            function: SCHEME.get_function("echo").unwrap(),
            args: [FunctionCallArgExpr::LhsFieldExpr(
                LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                    name: String::from("echo"),
                    function: SCHEME.get_function("echo").unwrap(),
                    args: vec![FunctionCallArgExpr::LhsFieldExpr(LhsFieldExpr::Field(
                        SCHEME.get_field_index("http.host").unwrap()
                    ))],
                })
            )]
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
                            }
                        ]
                    }
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
            mismatch: TypeMismatchError {
                actual: Type::Ip,
                expected: Type::Bytes,
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
}
