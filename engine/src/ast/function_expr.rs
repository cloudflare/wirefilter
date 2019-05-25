use crate::{
    ast::index_expr::IndexExpr,
    filter::CompiledValueExpr,
    functions::{
        FunctionArgKind, FunctionArgKindMismatchError, FunctionDefinition, FunctionOptArgCount,
        FunctionParam, InvalidFunctionArgError,
    },
    lex::{expect, skip_space, span, take_while, LexError, LexErrorKind, LexResult, LexWith},
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

    pub fn get_kind(&self) -> FunctionArgKind {
        match self {
            FunctionCallArgExpr::IndexExpr(_) => FunctionArgKind::Field,
            FunctionCallArgExpr::Literal(_) => FunctionArgKind::Literal,
        }
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        match self {
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

        let arg_counter = function.arg_count();
        let max_args = match arg_counter.optional {
            FunctionOptArgCount::Fixed(_) => arg_counter.count(),
            _ => args.len(),
        };

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
    let arg_counter = function.arg_count();
    (
        LexErrorKind::InvalidArgumentsCount {
            expected_min: arg_counter.required,
            expected_max: match arg_counter.optional {
                FunctionOptArgCount::Fixed(n) => Some(arg_counter.required + n),
                _ => None,
            },
        },
        input,
    )
}

impl<'s> GetType for FunctionCallExpr<'s> {
    fn get_type(&self) -> Type {
        self.function
            .return_type(&mut (&self.args).iter().map(|arg| FunctionParam {
                arg_kind: arg.get_kind(),
                arg_type: arg.get_type(),
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

        let arg_counter = function.arg_count();

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
                arg_type: arg.get_type(),
            };

            let param = function
                .validate(
                    &mut (&function_call.args).iter().map(|arg| FunctionParam {
                        arg_kind: arg.get_kind(),
                        arg_type: arg.get_type(),
                    }),
                    &next_param,
                )
                .or_else(|err| match err {
                    InvalidFunctionArgError::CountMismatch(_) => {
                        Err(invalid_args_count(function, input))
                    }
                    InvalidFunctionArgError::KindMismatch(err) => Err((
                        LexErrorKind::InvalidArgumentKind {
                            index: 0,
                            mismatch: err,
                        },
                        input,
                    )),
                    InvalidFunctionArgError::TypeMismatch(err) => Err((
                        LexErrorKind::InvalidArgumentType {
                            index: 0,
                            mismatch: err,
                        },
                        input,
                    )),
                })?;

            if next_param.arg_kind != param.arg_kind {
                return Err((
                    LexErrorKind::InvalidArgumentKind {
                        index,
                        mismatch: FunctionArgKindMismatchError {
                            actual: next_param.arg_kind,
                            expected: param.arg_kind,
                        },
                    },
                    span(input, rest),
                ));
            }

            if next_param.arg_type != param.arg_type {
                return Err((
                    LexErrorKind::InvalidArgumentType {
                        index,
                        mismatch: TypeMismatchError {
                            actual: next_param.arg_type,
                            expected: param.arg_type.into(),
                        },
                    },
                    span(input, rest),
                ));
            }

            params.push(param);

            function_call.args.push(arg);

            input = skip_space(rest);

            index += 1;
        }

        if function_call.args.len() < arg_counter.required {
            return Err(invalid_args_count(&function, input));
        }

        match arg_counter.optional {
            FunctionOptArgCount::Fixed(n)
                if function_call.args.len() > (arg_counter.required + n) =>
            {
                return Err(invalid_args_count(&function, input));
            }
            _ => {}
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
                            arg_type: Type::Bytes,
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
