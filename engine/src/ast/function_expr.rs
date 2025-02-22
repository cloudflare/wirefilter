use super::{
    parse::FilterParser,
    visitor::{Visitor, VisitorMut},
    ValueExpr,
};
use crate::{
    ast::{
        field_expr::{ComparisonExpr, ComparisonOp, ComparisonOpExpr},
        index_expr::IndexExpr,
        logical_expr::{LogicalExpr, UnaryOp},
    },
    compiler::Compiler,
    filter::{CompiledExpr, CompiledValueExpr, CompiledValueResult},
    functions::{
        ExactSizeChain, FunctionArgs, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
        FunctionParamError,
    },
    lex::{expect, skip_space, span, Lex, LexError, LexErrorKind, LexResult, LexWith},
    lhs_types::Array,
    scheme::Function,
    types::{GetType, LhsValue, RhsValue, Type},
};
use serde::Serialize;
use std::hash::{Hash, Hasher};
use std::iter::once;

/// Represents a function argument in a function call.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(tag = "kind", content = "value")]
pub enum FunctionCallArgExpr<'s> {
    /// A sub-expression which evaluates to a value.
    IndexExpr(IndexExpr<'s>),
    /// A literal value.
    Literal(RhsValue),
    /// A sub-expression which evaluates to either `true`/`false`
    /// or a list of `true`/`false`. It compiles to a [`CompiledExpr`]
    /// and is coerced into a [`CompiledValueExpr`]`.
    // Renaming is necessary for backward compability.
    #[serde(rename = "SimpleExpr")]
    Logical(LogicalExpr<'s>),
}

impl<'s> ValueExpr<'s> for FunctionCallArgExpr<'s> {
    #[inline]
    fn walk<'a, V: Visitor<'s, 'a>>(&'a self, visitor: &mut V) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => visitor.visit_index_expr(index_expr),
            FunctionCallArgExpr::Literal(_) => {}
            FunctionCallArgExpr::Logical(logical_expr) => visitor.visit_logical_expr(logical_expr),
        }
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'s, 'a>>(&'a mut self, visitor: &mut V) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => visitor.visit_index_expr(index_expr),
            FunctionCallArgExpr::Literal(_) => {}
            FunctionCallArgExpr::Logical(logical_expr) => visitor.visit_logical_expr(logical_expr),
        }
    }

    fn compile_with_compiler<C: Compiler<'s> + 's>(
        self,
        compiler: &mut C,
    ) -> CompiledValueExpr<'s, C::U> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => compiler.compile_index_expr(index_expr),
            FunctionCallArgExpr::Literal(literal) => {
                CompiledValueExpr::new(move |_| LhsValue::from(literal.clone()).into())
            }
            // The function argument is an expression compiled as either an
            // CompiledExpr::One or CompiledExpr::Vec.
            // Here we execute the expression to get the actual argument
            // for the function and forward the result in a CompiledValueExpr.
            FunctionCallArgExpr::Logical(logical_expr) => {
                let compiled_expr = compiler.compile_logical_expr(logical_expr);
                match compiled_expr {
                    CompiledExpr::One(expr) => {
                        CompiledValueExpr::new(move |ctx| LhsValue::from(expr.execute(ctx)).into())
                    }
                    CompiledExpr::Vec(expr) => CompiledValueExpr::new(move |ctx| {
                        let result = expr.execute(ctx);
                        LhsValue::Array(result.into()).into()
                    }),
                }
            }
        }
    }
}

impl FunctionCallArgExpr<'_> {
    pub(crate) fn map_each_count(&self) -> usize {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.map_each_count(),
            FunctionCallArgExpr::Literal(_) => 0,
            FunctionCallArgExpr::Logical(_) => 0,
        }
    }

    #[allow(dead_code)]
    pub(crate) fn simplify(self) -> Self {
        match self {
            FunctionCallArgExpr::Logical(LogicalExpr::Comparison(ComparisonExpr {
                lhs,
                op: ComparisonOpExpr::IsTrue,
            })) => FunctionCallArgExpr::IndexExpr(lhs),
            _ => self,
        }
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for FunctionCallArgExpr<'s> {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
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
            if c == '"' || (c == 'r' && (c2 == Some('#') || c2 == Some('"'))) {
                return RhsValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input));
            } else if c == '(' || UnaryOp::lex(input).is_ok() {
                return LogicalExpr::lex_with(input, parser)
                    .map(|(lhs, input)| (FunctionCallArgExpr::Logical(lhs), input));
            } else if c_is_field!(c)
                || (c_is_field_or_int!(c) && c2.is_some() && c_is_field!(c2.unwrap()))
                || (c_is_field_or_int!(c)
                    && c2.is_some()
                    && c_is_field_or_int!(c2.unwrap())
                    && c3.is_some()
                    && c_is_field!(c3.unwrap()))
            {
                let (lhs, input) = IndexExpr::lex_with(input, parser)?;
                let lookahead = skip_space(input);
                if ComparisonOp::lex(lookahead).is_ok() {
                    return ComparisonExpr::lex_with_lhs(input, parser, lhs).map(|(op, input)| {
                        (
                            FunctionCallArgExpr::Logical(LogicalExpr::Comparison(op)),
                            input,
                        )
                    });
                } else {
                    return Ok((FunctionCallArgExpr::IndexExpr(lhs), input));
                }
            }
        }

        // Fallback to blind parsing next argument
        if let Ok((lhs, input)) = IndexExpr::lex_with(input, parser) {
            let lookahead = skip_space(input);
            if ComparisonOp::lex(lookahead).is_ok() {
                return ComparisonExpr::lex_with_lhs(input, parser, lhs).map(|(op, input)| {
                    (
                        FunctionCallArgExpr::Logical(LogicalExpr::Comparison(op)),
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
            .map_err(|_| (LexErrorKind::EOF, _initial_input))
    }
}

impl GetType for FunctionCallArgExpr<'_> {
    fn get_type(&self) -> Type {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.get_type(),
            FunctionCallArgExpr::Literal(literal) => literal.get_type(),
            FunctionCallArgExpr::Logical(logical_expr) => logical_expr.get_type(),
        }
    }
}

impl<'a, 's> From<&'a FunctionCallArgExpr<'s>> for FunctionParam<'a> {
    fn from(arg_expr: &'a FunctionCallArgExpr<'s>) -> Self {
        match arg_expr {
            FunctionCallArgExpr::IndexExpr(expr) => FunctionParam::Variable(expr.get_type()),
            FunctionCallArgExpr::Logical(expr) => FunctionParam::Variable(expr.get_type()),
            FunctionCallArgExpr::Literal(value) => FunctionParam::Constant(value),
        }
    }
}

/// FunctionCallExpr represents a function call expression.
#[derive(Clone, Debug, Serialize)]
pub struct FunctionCallExpr<'s> {
    #[serde(rename = "name")]
    pub(crate) function: Function<'s>,
    pub(crate) args: Vec<FunctionCallArgExpr<'s>>,
    #[serde(skip)]
    pub(crate) context: Option<FunctionDefinitionContext>,
}

impl PartialEq for FunctionCallExpr<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function && self.args == other.args
    }
}

impl Eq for FunctionCallExpr<'_> {}

impl Hash for FunctionCallExpr<'_> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.function.hash(state);
        self.args.hash(state);
    }
}

impl<'s> ValueExpr<'s> for FunctionCallExpr<'s> {
    #[inline]
    fn walk<'a, V: Visitor<'s, 'a>>(&'a self, visitor: &mut V) {
        self.args
            .iter()
            .for_each(|arg| visitor.visit_function_call_arg_expr(arg));
        visitor.visit_function(&self.function)
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'s, 'a>>(&'a mut self, visitor: &mut V) {
        self.args
            .iter_mut()
            .for_each(|arg| visitor.visit_function_call_arg_expr(arg));
        visitor.visit_function(&self.function)
    }

    fn compile_with_compiler<C: Compiler<'s> + 's>(
        self,
        compiler: &mut C,
    ) -> CompiledValueExpr<'s, C::U> {
        let return_type = self.return_type();

        let Self {
            function,
            args,
            context,
            ..
        } = self;
        let map_each_count = args.first().map_or(0, |arg| arg.map_each_count());
        let call = function
            .as_definition()
            .compile(&mut args.iter().map(|arg| arg.into()), context);
        let mut args = args
            .into_iter()
            .map(|arg| compiler.compile_function_call_arg_expr(arg))
            .collect::<Vec<_>>();

        if map_each_count > 0 {
            let first = args.remove(0);

            #[inline(always)]
            fn compute<'s, 'a, I: ExactSizeIterator<Item = CompiledValueResult<'a>>>(
                first: CompiledValueResult<'a>,
                call: &(dyn for<'b> Fn(FunctionArgs<'_, 'b>) -> Option<LhsValue<'b>>
                      + Sync
                      + Send
                      + 's),
                return_type: Type,
                f: impl Fn(LhsValue<'a>) -> I,
            ) -> CompiledValueResult<'a> {
                let mut first = match first {
                    Ok(first) => first,
                    Err(_) => {
                        return Err(Type::Array(return_type.into()));
                    }
                };
                // Extract the values of the map
                if let LhsValue::Map(map) = first {
                    first = LhsValue::Array(
                        Array::try_from_iter(map.value_type(), map.values_into_iter()).unwrap(),
                    );
                }
                // Retrieve the underlying `Array`
                let mut first = match first {
                    LhsValue::Array(arr) => arr,
                    _ => unreachable!(),
                };
                if !first.is_empty() {
                    first = first.filter_map_to(return_type, |elem| call(&mut f(elem)));
                }
                Ok(LhsValue::Array(first))
            }

            if args.is_empty() {
                CompiledValueExpr::new(move |ctx| {
                    compute(
                        first.execute(ctx),
                        &call,
                        return_type,
                        #[inline]
                        |elem| once(Ok(elem)),
                    )
                })
            } else {
                CompiledValueExpr::new(move |ctx| {
                    compute(
                        first.execute(ctx),
                        &call,
                        return_type,
                        #[inline]
                        |elem| {
                            ExactSizeChain::new(
                                once(Ok(elem)),
                                args.iter().map(|arg| arg.execute(ctx)),
                            )
                        },
                    )
                })
            }
        } else {
            CompiledValueExpr::new(move |ctx| {
                if let Some(value) = call(&mut args.iter().map(|arg| arg.execute(ctx))) {
                    debug_assert!(value.get_type() == return_type);
                    Ok(value)
                } else {
                    Err(return_type)
                }
            })
        }
    }
}

impl<'s> FunctionCallExpr<'s> {
    pub(crate) fn new(
        function: Function<'s>,
        args: Vec<FunctionCallArgExpr<'s>>,
        context: Option<FunctionDefinitionContext>,
    ) -> Self {
        Self {
            function,
            args,
            context,
        }
    }

    pub(crate) fn lex_with_function<'i>(
        input: &'i str,
        parser: &FilterParser<'s>,
        function: Function<'s>,
    ) -> LexResult<'i, Self> {
        let definition = function.as_definition();

        let mut input = skip_space(input);

        input = expect(input, "(")?;

        input = skip_space(input);

        let (mandatory_arg_count, optional_arg_count) = definition.arg_count();

        let mut args: Vec<FunctionCallArgExpr<'s>> = Vec::new();

        let mut index = 0;

        let mut ctx = definition.context();

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

            let (arg, rest) = FunctionCallArgExpr::lex_with(input, parser)?;

            // Mapping is only accepted for the first argument
            // of a function call for code simplicity
            if arg.map_each_count() > 0 && index != 0 {
                return Err((LexErrorKind::InvalidMapEachAccess, span(input, rest)));
            }

            let next_param = (&arg).into();

            if optional_arg_count.is_some()
                && index >= (mandatory_arg_count + optional_arg_count.unwrap())
            {
                return Err(invalid_args_count(definition, input));
            }

            definition
                .check_param(
                    parser,
                    &mut args.iter().map(|arg| arg.into()),
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
            return Err(invalid_args_count(definition, input));
        }

        input = expect(input, ")")?;

        let function_call = FunctionCallExpr::new(function, args, ctx);

        Ok((function_call, input))
    }

    /// Returns the function being called.
    #[inline]
    pub fn function(&self) -> Function<'s> {
        self.function
    }

    /// Returns the arguments being passed to the function.
    #[inline]
    pub fn args(&self) -> &[FunctionCallArgExpr<'s>] {
        &self.args[..]
    }

    /// Returns the return type of the function call expression.
    #[inline]
    pub fn return_type(&self) -> Type {
        self.function.as_definition().return_type(
            &mut self.args.iter().map(|arg| arg.into()),
            self.context.as_ref(),
        )
    }

    /// Returns a reference to the function definition context.
    #[inline]
    pub fn context(&self) -> Option<&FunctionDefinitionContext> {
        self.context.as_ref()
    }

    /// Returns a mutable reference to the function definition context.
    #[inline]
    pub fn context_mut(&mut self) -> Option<&mut FunctionDefinitionContext> {
        self.context.as_mut()
    }
}

fn invalid_args_count<'i>(function: &dyn FunctionDefinition, input: &'i str) -> LexError<'i> {
    let (mandatory, optional) = function.arg_count();
    (
        LexErrorKind::InvalidArgumentsCount {
            expected_min: mandatory,
            expected_max: optional.map(|v| mandatory + v),
        },
        input,
    )
}

impl GetType for FunctionCallExpr<'_> {
    fn get_type(&self) -> Type {
        if !self.args.is_empty() && self.args[0].map_each_count() > 0 {
            Type::Array(self.return_type().into())
        } else {
            self.return_type()
        }
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for FunctionCallExpr<'s> {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (function, rest) = Function::lex_with(input, parser.scheme)?;

        Self::lex_with_function(rest, parser, function)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::{
            field_expr::{ComparisonExpr, ComparisonOpExpr, IdentifierExpr, OrderingOp},
            logical_expr::{LogicalExpr, LogicalOp, ParenthesizedExpr},
            parse::FilterParser,
        },
        functions::{
            FunctionArgKind, FunctionArgKindMismatchError, FunctionArgs, SimpleFunctionDefinition,
            SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam,
        },
        rhs_types::{Bytes, BytesFormat},
        scheme::{FieldIndex, IndexAccessError, Scheme},
        types::{RhsValues, Type, TypeMismatchError},
    };
    use std::convert::TryFrom;
    use std::sync::LazyLock;

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

    fn regex_replace<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
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
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i64::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    static SCHEME: LazyLock<Scheme> = LazyLock::new(|| {
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
                "any",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Array(Type::Bool.into()),
                    }],
                    opt_params: vec![],
                    return_type: Type::Bool,
                    implementation: SimpleFunctionImpl::new(any_function),
                },
            )
            .unwrap();
        scheme
            .add_function(
                "echo",
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
                "lower",
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
                "regex_replace",
                SimpleFunctionDefinition {
                    params: vec![
                        SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        },
                        SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Literal,
                            val_type: Type::Bytes,
                        },
                        SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Literal,
                            val_type: Type::Bytes,
                        },
                    ],
                    opt_params: vec![],
                    return_type: Type::Bool,
                    implementation: SimpleFunctionImpl::new(regex_replace),
                },
            )
            .unwrap();
        scheme
            .add_function(
                "len",
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
    });

    #[test]
    fn test_lex_function_call_expr() {
        // test that adjacent single digit int literals are parsed properly
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"echo ( http.host, 1, 2 );"#),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                ],
                context: None,
            },
            ";"
        );

        assert_eq!(expr.return_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bytes);

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
            FilterParser::new(&SCHEME).lex_as("echo ( http.host );"),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap()),
                    indexes: vec![],
                })],
                context: None,
            },
            ";"
        );

        assert_eq!(expr.return_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bytes);

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
            FilterParser::new(&SCHEME).lex_as(r#"echo (http.host,1,2);"#),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Int(1)),
                    FunctionCallArgExpr::Literal(RhsValue::Int(2)),
                ],
                context: None,
            },
            ";"
        );

        assert_eq!(expr.return_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bytes);

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
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>("echo ( );"),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(3),
            },
            ");"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( http.host , http.host );"),
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
            FilterParser::new(&SCHEME).lex_as("echo ( echo ( http.host ) );"),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: [FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            identifier: IdentifierExpr::Field(
                                SCHEME.get_field("http.host").unwrap()
                            ),
                            indexes: vec![],
                        })],
                        context: None,
                    }),
                    indexes: vec![],
                })]
                .to_vec(),
                context: None,
            },
            ";"
        );

        assert_eq!(expr.return_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bytes);

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
            FilterParser::new(&SCHEME).lex_as(
                r#"any ( ( http.request.headers.is_empty or http.request.headers.is_empty ) )"#
            ),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::Logical(LogicalExpr::Parenthesized(
                    Box::new(ParenthesizedExpr {
                        expr: LogicalExpr::Combining {
                            op: LogicalOp::Or,
                            items: vec![
                                LogicalExpr::Comparison(ComparisonExpr {
                                    lhs: IndexExpr {
                                        identifier: IdentifierExpr::Field(
                                            SCHEME
                                                .get_field("http.request.headers.is_empty")
                                                .unwrap()
                                        ),
                                        indexes: vec![],
                                    },
                                    op: ComparisonOpExpr::IsTrue,
                                }),
                                LogicalExpr::Comparison(ComparisonExpr {
                                    lhs: IndexExpr {
                                        identifier: IdentifierExpr::Field(
                                            SCHEME
                                                .get_field("http.request.headers.is_empty")
                                                .unwrap()
                                        ),
                                        indexes: vec![],
                                    },
                                    op: ComparisonOpExpr::IsTrue,
                                })
                            ]
                        }
                    })
                ))],
                context: None,
            },
            ""
        );

        assert_eq!(expr.return_type(), Type::Bool);
        assert_eq!(expr.get_type(), Type::Bool);

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
            FilterParser::new(&SCHEME).lex_as("echo ( http.request.headers.names[*] );"),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                })],
                context: None,
            },
            ";"
        );

        assert_eq!(expr.return_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Array(Type::Bytes.into()));

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
            FilterParser::new(&SCHEME).lex_as("echo ( http.headers[*] );"),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(SCHEME.get_field("http.headers").unwrap()),
                    indexes: vec![FieldIndex::MapEach],
                })],
                context: None,
            },
            ";"
        );

        assert_eq!(expr.return_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Array(Type::Bytes.into()));

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
            FilterParser::new(&SCHEME).lex_as("http.request.headers.names[*] == \"test\""),
            FunctionCallArgExpr::Logical(LogicalExpr::Comparison(ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(
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
            FilterParser::new(&SCHEME)
                .lex_as("any(lower(http.request.headers.names[*])[*] contains \"c\")"),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::Logical(LogicalExpr::Comparison(
                    ComparisonExpr {
                        lhs: IndexExpr {
                            identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                                function: SCHEME.get_function("lower").unwrap(),
                                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                                    identifier: IdentifierExpr::Field(
                                        SCHEME.get_field("http.request.headers.names").unwrap()
                                    ),
                                    indexes: vec![FieldIndex::MapEach],
                                })],
                                context: None,
                            }),
                            indexes: vec![FieldIndex::MapEach],
                        },
                        op: ComparisonOpExpr::Contains("c".to_string().into(),)
                    }
                ))],
                context: None,
            },
            ""
        );

        assert_eq!(expr.return_type(), Type::Bool);
        assert_eq!(expr.get_type(), Type::Bool);

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

        let expr = FunctionCallArgExpr::lex_with("lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(http.host)))))))))))))))))))))))))))))))) contains \"c\"", &FilterParser::new(&SCHEME));
        assert!(expr.is_ok());

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("len(http.request.headers.names[*])"),
            FunctionCallExpr {
                function: SCHEME.get_function("len").unwrap(),
                args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(
                        SCHEME.get_field("http.request.headers.names").unwrap()
                    ),
                    indexes: vec![FieldIndex::MapEach],
                })],
                context: None,
            },
            ""
        );

        assert_eq!(expr.args[0].map_each_count(), 1);
        assert_eq!(expr.return_type(), Type::Int);
        assert_eq!(expr.get_type(), Type::Array(Type::Int.into()));
    }

    #[test]
    fn test_lex_function_with_unary_expression_as_argument() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as("any(not(http.request.headers.names[*] in {\"Cookie\" \"Cookies\"}))"),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::Logical(LogicalExpr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(LogicalExpr::Parenthesized(Box::new(ParenthesizedExpr {
                        expr: LogicalExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                identifier: IdentifierExpr::Field(
                                    SCHEME.get_field("http.request.headers.names").unwrap()
                                ),
                                indexes: vec![FieldIndex::MapEach],
                            },
                            op: ComparisonOpExpr::OneOf(RhsValues::Bytes(vec![
                                "Cookie".to_owned().into(),
                                "Cookies".to_owned().into(),
                            ])),
                        })
                    },)))
                })],
                context: None,
            },
            ""
        );

        assert_eq!(expr.return_type(), Type::Bool);
        assert_eq!(expr.get_type(), Type::Bool);

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
            FilterParser::new(&SCHEME)
                .lex_as("any(!(http.request.headers.names[*] in {\"Cookie\" \"Cookies\"}))"),
            FunctionCallExpr {
                function: SCHEME.get_function("any").unwrap(),
                args: vec![FunctionCallArgExpr::Logical(LogicalExpr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(LogicalExpr::Parenthesized(Box::new(ParenthesizedExpr {
                        expr: LogicalExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                identifier: IdentifierExpr::Field(
                                    SCHEME.get_field("http.request.headers.names").unwrap()
                                ),
                                indexes: vec![FieldIndex::MapEach],
                            },
                            op: ComparisonOpExpr::OneOf(RhsValues::Bytes(vec![
                                "Cookie".to_owned().into(),
                                "Cookies".to_owned().into(),
                            ])),
                        })
                    },)))
                })],
                context: None,
            },
            ""
        );

        assert_eq!(expr.return_type(), Type::Bool);
        assert_eq!(expr.get_type(), Type::Bool);

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
    fn test_lex_function_call_raw_string() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("regex_replace(http.host, r\"this is a r##raw## string\", r\"this is a new r##raw## string\") eq \"test\""),
            FunctionCallExpr {
                function: SCHEME.get_function("regex_replace").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::new("this is a r##raw## string".as_bytes(), BytesFormat::Raw(0)))),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::new("this is a new r##raw## string".as_bytes(), BytesFormat::Raw(0))))
                ],
                context: None,
            },
            " eq \"test\""
        );

        assert_eq!(expr.return_type(), Type::Bool);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "name": "regex_replace",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": "this is a r##raw## string"
                    },
                    {
                        "kind": "Literal",
                        "value": "this is a new r##raw## string"
                    }
                ]
            }
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("regex_replace(http.host, r###\"this is a r##\"raw\"## string\"###, r###\"this is a new r##\"raw\"## string\"###) eq \"test\""),
            FunctionCallExpr {
                function: SCHEME.get_function("regex_replace").unwrap(),
                args: vec![
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap()),
                        indexes: vec![],
                    }),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::new("this is a r##\"raw\"## string".as_bytes(), BytesFormat::Raw(3)))),
                    FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::new("this is a new r##\"raw\"## string".as_bytes(), BytesFormat::Raw(3))))
                ],
                context: None,
            },
            " eq \"test\""
        );

        assert_eq!(expr.return_type(), Type::Bool);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "name": "regex_replace",
                "args": [
                    {
                        "kind": "IndexExpr",
                        "value": "http.host"
                    },
                    {
                        "kind": "Literal",
                        "value": "this is a r##\"raw\"## string"
                    },
                    {
                        "kind": "Literal",
                        "value": "this is a new r##\"raw\"## string"
                    }
                ]
            }
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>(
                "regex_replace(http.host, r#\"a\", \"b\") eq \"c\""
            ),
            LexErrorKind::MissingEndingQuote {},
            "#\"a\", \"b\") eq \"c\""
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>(
                "regex_replace(http.host, r\"a\"#, \"b\") eq \"c\""
            ),
            LexErrorKind::ExpectedLiteral(","),
            "#, \"b\") eq \"c\""
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>(
                "regex_replace(http.host, r##\"a\"#, \"b\") eq \"c\""
            ),
            LexErrorKind::MissingEndingQuote {},
            "##\"a\"#, \"b\") eq \"c\""
        );
    }

    #[test]
    fn test_lex_function_call_expr_failure() {
        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>("echo ( \"test\" );"),
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
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>("echo ( 10 );"),
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
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>("echo ( ip.addr );"),
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
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( http.host, 10, 2, \"test\" );"),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(3),
            },
            "\"test\" );"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>("echo ( http.test );"),
            LexErrorKind::UnknownIdentifier,
            "http.test"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( echo ( http.test ) );"),
            LexErrorKind::UnknownIdentifier,
            "http.test"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr<'_>>("echo ( http.host[*] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( http.request.headers.names[0][*] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( http.request.headers.names[*][0] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes,
            }),
            "[0]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( http.headers[*][\"host\"] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapKey("host".to_string()),
                actual: Type::Bytes,
            }),
            "[\"host\"]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr<'_>>("echo ( http.host, http.headers[*] );"),
            LexErrorKind::InvalidMapEachAccess,
            "http.headers[*]"
        );
    }
}
