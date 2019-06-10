use crate::{
    ast::{index_expr::IndexExpr, simple_expr::SimpleExpr, Expr},
    filter::{CompiledExpr, CompiledValueExpr},
    functions::{FunctionArgKind, FunctionDefinition, FunctionParam, FunctionParamError},
    lex::{expect, skip_space, span, take_while, LexError, LexErrorKind, LexResult, LexWith},
    scheme::{Field, Scheme},
    types::{Array, GetType, LhsValue, RhsValue, Type},
};
use derivative::Derivative;
use serde::Serialize;

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

    pub fn get_kind(&self) -> FunctionArgKind {
        match self {
            FunctionCallArgExpr::IndexExpr(_) => FunctionArgKind::Field,
            FunctionCallArgExpr::Literal(_) => FunctionArgKind::Literal,
            FunctionCallArgExpr::SimpleExpr(_) => FunctionArgKind::Field,
        }
    }

    pub fn compile(self) -> CompiledValueExpr<'s> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.compile(),
            FunctionCallArgExpr::Literal(literal) => {
                CompiledValueExpr::new(move |_| LhsValue::from(&literal).to_owned().into())
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
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let _initial_input = input;

        macro_rules! c_is_field {
            ($c:expr) => {
                (($c.is_ascii_alphanumeric() && !$c.is_ascii_hexdigit()) || $c == '_')
            };
        }

        // Grammar is ambiguous but lets try to parse the tokens we can be sure of
        // This will provide better error reporting in most cases
        let mut chars = input.chars();
        if let Some(c) = chars.next() {
            // check up to 3 next chars because third char of an hexa-string is either ':'
            // or '-'
            let c2 = chars.next();
            let c3 = chars.next();
            if c == '"' {
                return RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input));
            } else if c == '(' {
                return SimpleExpr::lex_with(input, scheme)
                    .map(|(lhs, input)| (FunctionCallArgExpr::SimpleExpr(lhs), input));
            } else if c_is_field!(c)
                || (c2.is_some() && c_is_field!(c2.unwrap()))
                || (c3.is_some() && c_is_field!(c3.unwrap()))
            {
                return IndexExpr::lex_with(input, scheme)
                    .map(|(lhs, input)| (FunctionCallArgExpr::IndexExpr(lhs), input));
            }
        }

        // Fallback to blind parsing next argument
        IndexExpr::lex_with(input, scheme)
            .map(|(lhs, input)| (FunctionCallArgExpr::IndexExpr(lhs), input))
            .or_else(|_| {
                SimpleExpr::lex_with(input, scheme)
                    .map(|(lhs, input)| (FunctionCallArgExpr::SimpleExpr(lhs), input))
            })
            .or_else(|_| {
                RhsValue::lex_with(input, Type::Ip)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
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

        let function = scheme
            .get_function(name)
            .map_err(|err| (LexErrorKind::UnknownFunction(err), initial_input))?;

        input = skip_space(input);

        input = expect(input, "(")?;

        input = skip_space(input);

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{
            combined_expr::{CombinedExpr, CombiningOp},
            field_expr::{FieldExpr, FieldOp, LhsFieldExpr},
        },
        functions::{
            Function, FunctionArgKindMismatchError, FunctionArgs, FunctionImpl, FunctionOptParam,
        },
        scheme::UnknownFieldError,
        types::{Array, Type, TypeMismatchError},
    };
    use lazy_static::lazy_static;
    use std::convert::TryFrom;

    // test function
    fn any_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        let arg = match args.next() {
            Some(Ok(arg)) => match args.next() {
                Some(_) => unreachable!(),
                None => arg,
            },
            _ => unreachable!(),
        };
        Some(LhsValue::Bool(
            Array::try_from(arg)
                .unwrap()
                .into_iter()
                .any(|lhs| bool::try_from(lhs).unwrap()),
        ))
    }

    // test function
    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.host: Bytes,
                http.request.headers.keys: Array(Bytes),
                http.request.headers.values: Array(Bytes),
                http.request.headers.is_empty: Array(Bool),
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
            };
            scheme
                .add_function(
                    "any".into(),
                    Function {
                        params: vec![FunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Array(Box::new(Type::Bool)),
                        }],
                        opt_params: vec![],
                        return_type: Type::Bool,
                        implementation: FunctionImpl::new(any_function),
                    },
                )
                .unwrap();
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

    #[test]
    fn test_lex_function_call_expr() {
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
            LexErrorKind::UnknownField(UnknownFieldError),
            "http.test"
        );

        assert_err!(
            FunctionCallExpr::lex_with("echo ( echo ( http.test ) );", &SCHEME),
            LexErrorKind::UnknownField(UnknownFieldError),
            "http.test"
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
                    Box::new(CombinedExpr::Combining {
                        op: CombiningOp::Or,
                        items: vec![
                            CombinedExpr::Simple(SimpleExpr::Field(FieldExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME
                                            .get_field_index("http.request.headers.is_empty")
                                            .unwrap()
                                    ),
                                    indexes: vec![],
                                },
                                op: FieldOp::IsTrue,
                            })),
                            CombinedExpr::Simple(SimpleExpr::Field(FieldExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(
                                        SCHEME
                                            .get_field_index("http.request.headers.is_empty")
                                            .unwrap()
                                    ),
                                    indexes: vec![],
                                },
                                op: FieldOp::IsTrue,
                            }))
                        ]
                    })
                ))],
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
    }
}
