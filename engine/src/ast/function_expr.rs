use super::field_expr::LhsFieldExpr;
use execution_context::ExecutionContext;
use functions::{Function, FunctionArg};
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

struct SchemeFunctionArg<'s> {
    scheme: &'s Scheme,
    funcarg: &'s FunctionArg,
}

impl<'i, 's> LexWith<'i, SchemeFunctionArg<'s>> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, scheme_funcarg: SchemeFunctionArg<'s>) -> LexResult<'i, Self> {
        let initial_input = input;

        match *scheme_funcarg.funcarg {
            FunctionArg::Field(ty) => {
                let (lhs, input) = LhsFieldExpr::lex_with(input, scheme_funcarg.scheme)?;
                if lhs.get_type() != ty {
                    Err((
                        LexErrorKind::InvalidArgumentType {
                            given: lhs.get_type(),
                            expected: ty,
                        },
                        initial_input,
                    ))
                } else {
                    Ok((FunctionCallArgExpr::LhsFieldExpr(lhs), input))
                }
            }
            FunctionArg::Literal(ty) => {
                let (rhs_value, input) = RhsValue::lex_with(input, ty)?;
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

        let lookahead = take(input, 1)?.0.chars().next().unwrap();

        if lookahead != ')' {
            let mut i = 0;

            loop {
                let arg_def = match function.args.get(i) {
                    Some(def) => def,
                    None => {
                        return Err((
                            LexErrorKind::IncompatibleNumberArguments {
                                expected: function.args.len(),
                            },
                            input,
                        ));
                    }
                };

                let arg = FunctionCallArgExpr::lex_with(
                    input,
                    SchemeFunctionArg {
                        scheme,
                        funcarg: arg_def,
                    },
                )?;

                function_call.args.push(arg.0);

                input = skip_space(arg.1);

                match expect(input, ",") {
                    Ok(rest) => input = skip_space(rest),
                    Err(_) => break,
                };

                i += 1;
            }

            input = expect(input, ")")?;
        }

        if function.args.len() != function_call.args.len() {
            return Err((
                LexErrorKind::IncompatibleNumberArguments {
                    expected: function.args.len(),
                },
                input,
            ));
        }

        Ok((function_call, input))
    }
}

#[test]
fn test_function() {
    use functions::FunctionImpl;
    use lazy_static::lazy_static;
    use scheme::UnknownFieldError;
    use types::Type;

    fn echo_function<'a>(args: &[LhsValue<'a>]) -> LhsValue<'a> {
        let input = &args[0];
        match input {
            LhsValue::Bytes(bytes) => LhsValue::Bytes(bytes.to_vec().into()),
            _ => panic!("Invalid type: expected Bytes, got {:?}", input),
        }
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
                        args: vec![FunctionArg::Field(Type::Bytes)],
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
        LexErrorKind::IncompatibleNumberArguments { expected: 1 },
        ");"
    );

    assert_err!(
        FunctionCallExpr::lex_with("echo ( http.host , http.host );", &SCHEME),
        LexErrorKind::IncompatibleNumberArguments { expected: 1 },
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
            given: Type::Ip,
            expected: Type::Bytes
        },
        "ip.addr );"
    );
}
