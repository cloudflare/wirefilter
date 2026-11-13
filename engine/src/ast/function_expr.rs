use super::ValueExpr;
use super::parse::FilterParser;
use super::visitor::{Visitor, VisitorMut};
use crate::FunctionRef;
use crate::ast::field_expr::{ComparisonExpr, ComparisonOp, ComparisonOpExpr, IdentifierExpr};
use crate::ast::index_expr::IndexExpr;
use crate::ast::logical_expr::{LogicalExpr, QuantifierOp, UnaryOp};
use crate::compiler::Compiler;
use crate::filter::{CompiledExpr, CompiledValueExpr, CompiledValueResult};
use crate::functions::{
    CompiledFunction, ExactSizeChain, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
    FunctionParamError,
};
use crate::lex::{Lex, LexError, LexErrorKind, LexResult, LexWith, expect, skip_space, span};
use crate::lhs_types::Array;
use crate::scheme::Function;
use crate::types::{GetType, LhsValue, LiteralValue, Type};
use serde::Serialize;
use std::hash::{Hash, Hasher};
use std::iter::once;

/// Represents a function argument in a function call.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(tag = "kind", content = "value")]
pub enum FunctionCallArgExpr {
    /// A sub-expression which evaluates to a value.
    IndexExpr(IndexExpr),
    /// A literal value.
    Literal(LiteralValue),
    /// A sub-expression which evaluates to either `true`/`false`
    /// or a list of `true`/`false`. It compiles to a [`CompiledExpr`]
    /// and is coerced into a [`CompiledValueExpr`]`.
    // Renaming is necessary for backward compability.
    #[serde(rename = "SimpleExpr")]
    Logical(LogicalExpr),
}

impl ValueExpr for FunctionCallArgExpr {
    #[inline]
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => visitor.visit_index_expr(index_expr),
            FunctionCallArgExpr::Literal(_) => {}
            FunctionCallArgExpr::Logical(logical_expr) => visitor.visit_logical_expr(logical_expr),
        }
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => visitor.visit_index_expr(index_expr),
            FunctionCallArgExpr::Literal(_) => {}
            FunctionCallArgExpr::Logical(logical_expr) => visitor.visit_logical_expr(logical_expr),
        }
    }

    fn compile_with_compiler<C: Compiler>(
        self,
        compiler: &mut C,
    ) -> CompiledValueExpr<C::U, C::Family> {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => compiler.compile_index_expr(index_expr),
            FunctionCallArgExpr::Literal(LiteralValue::Bytes(bytes)) => {
                // Formatting is only needed by the AST. Keep the payload and
                // clone it on access so the result can outlive this expression.
                let bytes: Box<[u8]> = bytes.into();
                CompiledValueExpr::new(move |_| LhsValue::from(bytes.clone()).into())
            }
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
                    CompiledExpr::Vec(expr) => CompiledValueExpr::new_with_context(move |ctx| {
                        let ctx = ctx.context();
                        let result = expr.execute(ctx);
                        LhsValue::Array(result.into()).into()
                    }),
                }
            }
        }
    }
}

impl FunctionCallArgExpr {
    pub(crate) fn map_each_count(&self) -> usize {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.map_each_count(),
            FunctionCallArgExpr::Literal(_) => 0,
            FunctionCallArgExpr::Logical(_) => 0,
        }
    }

    /// Returns `true` if re-evaluating this argument for every mapped element
    /// could be costly, i.e. it is a nested function call or a logical
    /// sub-expression. Literals and stored field accesses are cheap to evaluate
    /// repeatedly. Native field conversion is classified separately at binding.
    fn is_expensive_to_reevaluate(&self) -> bool {
        match self {
            FunctionCallArgExpr::Literal(_) => false,
            FunctionCallArgExpr::Logical(_) => true,
            FunctionCallArgExpr::IndexExpr(index_expr) => {
                matches!(index_expr.identifier, IdentifierExpr::FunctionCallExpr(_))
            }
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

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for FunctionCallArgExpr {
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
                return LiteralValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input));
            } else if c == '('
                || UnaryOp::lex(input).is_ok()
                || QuantifierOp::lex_call(input).is_some()
            {
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

        LiteralValue::lex_with(input, Type::Ip)
            .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            .or_else(|_| {
                LiteralValue::lex_with(input, Type::Int)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            // try to parse Bytes after Int because digit literals < 255 are wrongly
            // interpreted as Bytes
            .or_else(|_| {
                LiteralValue::lex_with(input, Type::Bytes)
                    .map(|(literal, input)| (FunctionCallArgExpr::Literal(literal), input))
            })
            .map_err(|_| (LexErrorKind::EOF, _initial_input))
    }
}

impl GetType for FunctionCallArgExpr {
    fn get_type(&self) -> Type {
        match self {
            FunctionCallArgExpr::IndexExpr(index_expr) => index_expr.get_type(),
            FunctionCallArgExpr::Literal(literal) => literal.get_type(),
            FunctionCallArgExpr::Logical(logical_expr) => logical_expr.get_type(),
        }
    }
}

impl<'a> From<&'a FunctionCallArgExpr> for FunctionParam<'a> {
    fn from(arg_expr: &'a FunctionCallArgExpr) -> Self {
        match arg_expr {
            FunctionCallArgExpr::IndexExpr(expr) => FunctionParam::Variable(expr.get_type()),
            FunctionCallArgExpr::Logical(expr) => FunctionParam::Variable(expr.get_type()),
            FunctionCallArgExpr::Literal(value) => FunctionParam::Constant(value),
        }
    }
}

/// FunctionCallExpr represents a function call expression.
#[derive(Clone, Debug, Serialize)]
pub struct FunctionCallExpr {
    #[serde(rename = "name")]
    pub(crate) function: Function,
    pub(crate) args: Box<[FunctionCallArgExpr]>,
    #[serde(skip)]
    pub(crate) context: Option<FunctionDefinitionContext>,
}

impl PartialEq for FunctionCallExpr {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.function == other.function && self.args == other.args
    }
}

impl Eq for FunctionCallExpr {}

impl Hash for FunctionCallExpr {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.function.hash(state);
        self.args.hash(state);
    }
}

impl ValueExpr for FunctionCallExpr {
    #[inline]
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        self.args
            .iter()
            .for_each(|arg| visitor.visit_function_call_arg_expr(arg));
        visitor.visit_function(&self.function)
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        self.args
            .iter_mut()
            .for_each(|arg| visitor.visit_function_call_arg_expr(arg));
        visitor.visit_function(&self.function)
    }

    fn compile_with_compiler<C: Compiler>(
        self,
        compiler: &mut C,
    ) -> CompiledValueExpr<C::U, C::Family> {
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
        // For `map_each`, only bother evaluating the non-mapped arguments once
        // (instead of once per element) when at least one of them is expensive
        // to re-evaluate. For trivial arguments (literals / stored field
        // accesses) inline re-evaluation is just as cheap and avoids a
        // per-call allocation.
        let memoize_extra_args = map_each_count > 0
            && args
                .iter()
                .skip(1)
                .any(FunctionCallArgExpr::is_expensive_to_reevaluate);
        // Native field values can require whole-container conversion, including
        // when an index subsequently selects one scalar. Classify the provider
        // during compilation so ordinary stored field accesses stay cheap.
        let memoize_native_extra_args = map_each_count > 0
            && !memoize_extra_args
            && args.iter().skip(1).any(|arg| {
                matches!(arg, FunctionCallArgExpr::IndexExpr(index)
                    if index.materializes_collection(compiler))
            });
        let mut args = args
            .into_iter()
            .map(|arg| compiler.compile_function_call_arg_expr(arg));

        if map_each_count > 0 {
            let first = args.next().unwrap();
            let args = args.collect::<Box<[_]>>();

            #[inline(always)]
            fn compute<'a, I: ExactSizeIterator<Item = CompiledValueResult<'a>>>(
                first: CompiledValueResult<'a>,
                call: &CompiledFunction,
                return_type: Type,
                f: impl Fn(LhsValue<'a>) -> I,
            ) -> CompiledValueResult<'a> {
                let first = match first {
                    Ok(first) => first,
                    Err(_) => {
                        return Err(Type::Array(return_type.into()));
                    }
                };
                let result = match first {
                    // Map the values straight into the result array. This avoids
                    // the intermediate `Array` allocation (and per-element type
                    // re-check) that a separate map -> array conversion followed
                    // by `filter_map_to` would incur.
                    LhsValue::Map(map) => {
                        // Reserve up front for the whole map: `filter_map`'s
                        // `size_hint` lower bound is 0, and `map_each` rarely
                        // filters, so this avoids repeated reallocations.
                        let len = map.len();
                        Array::try_from_iter_with_capacity(
                            return_type,
                            len,
                            map.into_values().filter_map(|elem| call(&mut f(elem))),
                        )
                        .unwrap()
                    }
                    LhsValue::Array(mut arr) => {
                        if !arr.is_empty() {
                            arr = arr.filter_map_to(return_type, |elem| call(&mut f(elem)));
                        }
                        arr
                    }
                    _ => unreachable!(),
                };
                Ok(LhsValue::Array(result))
            }

            if args.is_empty() {
                CompiledValueExpr::new_with_context(move |ctx| {
                    let ctx = ctx.context();
                    compute(
                        first.execute(ctx),
                        &call,
                        return_type,
                        #[inline]
                        |elem| once(Ok(elem)),
                    )
                })
            } else if memoize_extra_args {
                CompiledValueExpr::new_with_context(move |ctx| {
                    let ctx = ctx.context();
                    // At least one non-mapped argument is expensive to
                    // re-evaluate, so evaluate all of them once per call and
                    // reuse them (cheaply cloned) for every element instead of
                    // re-executing the argument expressions for every element.
                    let extra_args = args
                        .iter()
                        .map(|arg| arg.execute(ctx))
                        .collect::<Box<[_]>>();
                    compute(
                        first.execute(ctx),
                        &call,
                        return_type,
                        #[inline]
                        |elem| ExactSizeChain::new(once(Ok(elem)), extra_args.iter().cloned()),
                    )
                })
            } else if memoize_native_extra_args {
                CompiledValueExpr::new_with_context(move |ctx| {
                    let ctx = ctx.context();
                    // Preserve lazy argument consumption: empty mapped inputs
                    // and functions that ignore an argument must not read it.
                    // Cloning cached LhsValues retains the function interface's
                    // ownership contract, but native conversion runs only once.
                    let extra_args = std::cell::OnceCell::new();
                    compute(first.execute(ctx), &call, return_type, |elem| {
                        let values = extra_args.get_or_init(|| {
                            (0..args.len())
                                .map(|_| std::cell::OnceCell::new())
                                .collect::<Box<[_]>>()
                        });
                        ExactSizeChain::new(
                            once(Ok(elem)),
                            args.iter()
                                .zip(values.iter())
                                .map(|(arg, value)| value.get_or_init(|| arg.execute(ctx)).clone()),
                        )
                    })
                })
            } else {
                CompiledValueExpr::new_with_context(move |ctx| {
                    let ctx = ctx.context();
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
            let args = args.collect::<Box<[_]>>();
            CompiledValueExpr::new_with_context(move |ctx| {
                let ctx = ctx.context();
                match call(&mut args.iter().map(|arg| arg.execute(ctx))) {
                    Some(value) => {
                        debug_assert!(value.get_type() == return_type);
                        Ok(value)
                    }
                    _ => Err(return_type),
                }
            })
        }
    }
}

impl FunctionCallExpr {
    pub(crate) fn new(
        function: Function,
        args: Box<[FunctionCallArgExpr]>,
        context: Option<FunctionDefinitionContext>,
    ) -> Self {
        Self {
            function: function.to_owned(),
            args,
            context,
        }
    }

    pub(crate) fn lex_with_function<'i>(
        input: &'i str,
        parser: &FilterParser<'_>,
        function: FunctionRef<'_>,
    ) -> LexResult<'i, Self> {
        let definition = function.as_definition();

        let mut input = skip_space(input);

        input = expect(input, "(")?;

        input = skip_space(input);

        let (mandatory_arg_count, optional_arg_count) = definition.arg_count();

        let mut args: Vec<FunctionCallArgExpr> = Vec::new();

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
                    parser.settings(),
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

        let function_call =
            FunctionCallExpr::new(function.to_owned(), args.into_boxed_slice(), ctx);

        Ok((function_call, input))
    }

    /// Returns the function being called.
    #[inline]
    pub fn function(&self) -> FunctionRef<'_> {
        self.function.as_ref()
    }

    /// Returns the arguments being passed to the function.
    #[inline]
    pub fn args(&self) -> &[FunctionCallArgExpr] {
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

impl GetType for FunctionCallExpr {
    fn get_type(&self) -> Type {
        if !self.args.is_empty() && self.args[0].map_each_count() > 0 {
            Type::Array(self.return_type().into())
        } else {
            self.return_type()
        }
    }
}

impl<'i> LexWith<'i, &FilterParser<'_>> for FunctionCallExpr {
    fn lex_with(input: &'i str, parser: &FilterParser<'_>) -> LexResult<'i, Self> {
        let (function, rest) = FunctionRef::lex_with(input, parser.scheme)?;
        let nested_parser = parser.with_increased_nesting(skip_space(rest))?;

        Self::lex_with_function(rest, &nested_parser, function)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::SimpleFunctionArgKind;
    use crate::ast::field_expr::{
        ComparisonExpr, ComparisonOpExpr, ComparisonRhs, IdentifierExpr, OrderingOp,
    };
    use crate::ast::logical_expr::{
        LogicalExpr, LogicalOp, ParenthesizedExpr, QuantifierArgExpr, QuantifierOp,
    };
    use crate::ast::parse::FilterParser;
    use crate::functions::{
        FunctionArgKind, FunctionArgKindMismatchError, FunctionArgs, SimpleFunctionDefinition,
        SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam,
    };
    use crate::rhs_types::{BytesExpr, BytesFormat};
    use crate::scheme::{FieldIndex, IndexAccessError, Scheme};
    use crate::types::{LiteralSet, Type, TypeMismatchError};
    use std::convert::TryFrom;
    use std::sync::LazyLock;

    fn regex_replace<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    fn lower_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(mut b)) => {
                b.to_mut().make_ascii_lowercase();
                Some(LhsValue::Bytes(b))
            }
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    #[test]
    fn test_function_call_nesting_limit() {
        let mut parser = FilterParser::new(&SCHEME);
        parser.set_max_nesting_depth(2);

        assert_err!(
            parser.lex_as::<FunctionCallExpr>("echo ( echo ( echo ( http.host ) ) )"),
            LexErrorKind::NestingLimitExceeded { limit: 2 },
            "( http.host ) ) )"
        );
    }

    #[test]
    fn test_value_expr_function_call_nesting_limit() {
        let mut parser = FilterParser::new(&SCHEME);
        parser.set_max_nesting_depth(2);

        assert_err!(
            parser.lex_as::<crate::FilterValueAst>("echo ( echo ( echo ( http.host ) ) )"),
            LexErrorKind::NestingLimitExceeded { limit: 2 },
            "( http.host ) ) )"
        );
    }

    #[test]
    fn test_logical_argument_nesting_limit_is_counted_via_function_and_parentheses() {
        let mut parser = FilterParser::new(&SCHEME);
        parser.set_max_nesting_depth(1);

        assert_err!(
            parser.lex_as::<LogicalExpr>(
                "any ( ( http.request.headers.is_empty or http.request.headers.is_empty ) )"
            ),
            LexErrorKind::NestingLimitExceeded { limit: 1 },
            "( http.request.headers.is_empty or http.request.headers.is_empty ) )"
        );
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i64::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    static SCHEME: LazyLock<Scheme> = LazyLock::new(|| {
        let mut builder = Scheme! {
            http.headers: Map(Bytes),
            http.host: Bytes,
            http.request.headers.names: Array(Bytes),
            http.request.headers.values: Array(Bytes),
            http.request.headers.is_empty: Array(Bool),
            ip.addr: Ip,
            ssl: Bool,
            tcp.port: Int,
        };
        builder
            .add_function(
                "echo",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }]),
                    opt_params: Box::new([
                        SimpleFunctionOptParam {
                            arg_kind: SimpleFunctionArgKind::Literal,
                            default_value: LhsValue::Int(10),
                        },
                        SimpleFunctionOptParam {
                            arg_kind: SimpleFunctionArgKind::Literal,
                            default_value: LhsValue::Int(1),
                        },
                    ]),
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(echo_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "lower",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }]),
                    opt_params: Box::new([]),
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(lower_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "regex_replace",
                SimpleFunctionDefinition {
                    params: Box::new([
                        SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Field,
                            val_type: Type::Bytes,
                        },
                        SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Literal,
                            val_type: Type::Bytes,
                        },
                        SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Literal,
                            val_type: Type::Bytes,
                        },
                    ]),
                    opt_params: Box::new([]),
                    return_type: Type::Bool,
                    implementation: SimpleFunctionImpl::new(regex_replace),
                },
            )
            .unwrap();
        builder
            .add_function(
                "len",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }]),
                    opt_params: Box::new([]),
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(len_function),
                },
            )
            .unwrap();
        builder.build()
    });

    #[test]
    fn test_lex_function_call_expr() {
        // test that adjacent single digit int literals are parsed properly
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"echo ( http.host, 1, 2 );"#),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap().to_owned(),
                args: Box::new([
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("http.host").unwrap().to_owned()
                        ),
                        indexes: Box::new([]),
                    }),
                    FunctionCallArgExpr::Literal(LiteralValue::Int(1)),
                    FunctionCallArgExpr::Literal(LiteralValue::Int(2)),
                ]),
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
                function: SCHEME.get_function("echo").unwrap().to_owned(),
                args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(
                        SCHEME.get_field("http.host").unwrap().to_owned()
                    ),
                    indexes: Box::new([]),
                })]),
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
                function: SCHEME.get_function("echo").unwrap().to_owned(),
                args: Box::new([
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(
                            SCHEME.get_field("http.host").unwrap().to_owned()
                        ),
                        indexes: Box::new([]),
                    }),
                    FunctionCallArgExpr::Literal(LiteralValue::Int(1)),
                    FunctionCallArgExpr::Literal(LiteralValue::Int(2)),
                ]),
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
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( );"),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(3),
            },
            ");"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("echo ( http.host , http.host );"),
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
                function: SCHEME.get_function("echo").unwrap().to_owned(),
                args: [FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("echo").unwrap().to_owned(),
                        args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                            identifier: IdentifierExpr::Field(
                                SCHEME.get_field("http.host").unwrap().to_owned()
                            ),
                            indexes: Box::new([]),
                        })]),
                        context: None,
                    }),
                    indexes: Box::new([]),
                })]
                .to_vec()
                .into_boxed_slice(),
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
            LogicalExpr::Quantifier {
                op: QuantifierOp::Any,
                arg: Box::new(QuantifierArgExpr::Logical(LogicalExpr::Parenthesized(
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
                                                .to_owned()
                                        ),
                                        indexes: Box::new([]),
                                    },
                                    op: ComparisonOpExpr::IsTrue,
                                }),
                                LogicalExpr::Comparison(ComparisonExpr {
                                    lhs: IndexExpr {
                                        identifier: IdentifierExpr::Field(
                                            SCHEME
                                                .get_field("http.request.headers.is_empty")
                                                .unwrap()
                                                .to_owned()
                                        ),
                                        indexes: Box::new([]),
                                    },
                                    op: ComparisonOpExpr::IsTrue,
                                })
                            ]
                        }
                    })
                ))),
            },
            ""
        );

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "op": "Any",
                "arg": {
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
            }
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("echo ( http.request.headers.names[*] );"),
            FunctionCallExpr {
                function: SCHEME.get_function("echo").unwrap().to_owned(),
                args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(
                        SCHEME
                            .get_field("http.request.headers.names")
                            .unwrap()
                            .to_owned()
                    ),
                    indexes: Box::new([FieldIndex::MapEach]),
                })]),
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
                function: SCHEME.get_function("echo").unwrap().to_owned(),
                args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(
                        SCHEME.get_field("http.headers").unwrap().to_owned()
                    ),
                    indexes: Box::new([FieldIndex::MapEach]),
                })]),
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
                        SCHEME
                            .get_field("http.request.headers.names")
                            .unwrap()
                            .to_owned()
                    ),
                    indexes: Box::new([FieldIndex::MapEach]),
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("test".to_owned().into()))
                }
            })),
            ""
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as("any(lower(http.request.headers.names[*])[*] contains \"c\")"),
            LogicalExpr::Quantifier {
                op: QuantifierOp::Any,
                arg: Box::new(QuantifierArgExpr::Logical(LogicalExpr::Comparison(
                    ComparisonExpr {
                        lhs: IndexExpr {
                            identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                                function: SCHEME.get_function("lower").unwrap().to_owned(),
                                args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                                    identifier: IdentifierExpr::Field(
                                        SCHEME
                                            .get_field("http.request.headers.names")
                                            .unwrap()
                                            .to_owned()
                                    ),
                                    indexes: Box::new([FieldIndex::MapEach]),
                                })]),
                                context: None,
                            }),
                            indexes: Box::new([FieldIndex::MapEach]),
                        },
                        op: ComparisonOpExpr::Contains("c".to_string().into(),)
                    }
                ))),
            },
            ""
        );

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "op": "Any",
                "arg": {
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
            }
        );

        let expr = FunctionCallArgExpr::lex_with(
            "lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(lower(http.host)))))))))))))))))))))))))))))))) contains \"c\"",
            &FilterParser::new(&SCHEME),
        );
        assert!(expr.is_ok());

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("len(http.request.headers.names[*])"),
            FunctionCallExpr {
                function: SCHEME.get_function("len").unwrap().to_owned(),
                args: Box::new([FunctionCallArgExpr::IndexExpr(IndexExpr {
                    identifier: IdentifierExpr::Field(
                        SCHEME
                            .get_field("http.request.headers.names")
                            .unwrap()
                            .to_owned()
                    ),
                    indexes: Box::new([FieldIndex::MapEach]),
                })]),
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
            LogicalExpr::Quantifier {
                op: QuantifierOp::Any,
                arg: Box::new(QuantifierArgExpr::Logical(LogicalExpr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(LogicalExpr::Parenthesized(Box::new(ParenthesizedExpr {
                        expr: LogicalExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                identifier: IdentifierExpr::Field(
                                    SCHEME
                                        .get_field("http.request.headers.names")
                                        .unwrap()
                                        .to_owned()
                                ),
                                indexes: Box::new([FieldIndex::MapEach]),
                            },
                            op: ComparisonOpExpr::OneOf(LiteralSet::Bytes(vec![
                                "Cookie".to_owned().into(),
                                "Cookies".to_owned().into(),
                            ])),
                        })
                    },)))
                })),
            },
            ""
        );

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "op": "Any",
                "arg": {
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
            }
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as("any(!(http.request.headers.names[*] in {\"Cookie\" \"Cookies\"}))"),
            LogicalExpr::Quantifier {
                op: QuantifierOp::Any,
                arg: Box::new(QuantifierArgExpr::Logical(LogicalExpr::Unary {
                    op: UnaryOp::Not,
                    arg: Box::new(LogicalExpr::Parenthesized(Box::new(ParenthesizedExpr {
                        expr: LogicalExpr::Comparison(ComparisonExpr {
                            lhs: IndexExpr {
                                identifier: IdentifierExpr::Field(
                                    SCHEME
                                        .get_field("http.request.headers.names")
                                        .unwrap()
                                        .to_owned()
                                ),
                                indexes: Box::new([FieldIndex::MapEach]),
                            },
                            op: ComparisonOpExpr::OneOf(LiteralSet::Bytes(vec![
                                "Cookie".to_owned().into(),
                                "Cookies".to_owned().into(),
                            ])),
                        })
                    },)))
                })),
            },
            ""
        );

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "op": "Any",
                "arg": {
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
            }
        );
    }

    #[test]
    fn test_lex_function_call_raw_string() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("regex_replace(http.host, r\"this is a r##raw## string\", r\"this is a new r##raw## string\") eq \"test\""),
            FunctionCallExpr {
                function: SCHEME.get_function("regex_replace").unwrap().to_owned(),
                args: Box::new([
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap().to_owned()),
                        indexes: Box::new([]),
                    }),
                    FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::new("this is a r##raw## string".as_bytes(), BytesFormat::Raw(0)))),
                    FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::new("this is a new r##raw## string".as_bytes(), BytesFormat::Raw(0))))
                ]),
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
                function: SCHEME.get_function("regex_replace").unwrap().to_owned(),
                args: Box::new([
                    FunctionCallArgExpr::IndexExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(SCHEME.get_field("http.host").unwrap().to_owned()),
                        indexes: Box::new([]),
                    }),
                    FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::new("this is a r##\"raw\"## string".as_bytes(), BytesFormat::Raw(3)))),
                    FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::new("this is a new r##\"raw\"## string".as_bytes(), BytesFormat::Raw(3))))
                ]),
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
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("regex_replace(http.host, r#\"a\", \"b\") eq \"c\""),
            LexErrorKind::MissingEndingQuote {},
            "#\"a\", \"b\") eq \"c\""
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("regex_replace(http.host, r\"a\"#, \"b\") eq \"c\""),
            LexErrorKind::ExpectedLiteral(","),
            "#, \"b\") eq \"c\""
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("regex_replace(http.host, r##\"a\"#, \"b\") eq \"c\""),
            LexErrorKind::MissingEndingQuote {},
            "##\"a\"#, \"b\") eq \"c\""
        );
    }

    #[test]
    fn test_lex_function_call_expr_failure() {
        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( \"test\" );"),
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
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( 10 );"),
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
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( ip.addr );"),
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
                .lex_as::<FunctionCallExpr>("echo ( http.host, 10, 2, \"test\" );"),
            LexErrorKind::InvalidArgumentsCount {
                expected_min: 1,
                expected_max: Some(3),
            },
            "\"test\" );"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( http.test );"),
            LexErrorKind::UnknownIdentifier,
            "http.test"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( echo ( http.test ) );"),
            LexErrorKind::UnknownIdentifier,
            "http.test"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<FunctionCallExpr>("echo ( http.host[*] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("echo ( http.request.headers.names[0][*] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("echo ( http.request.headers.names[*][0] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::ArrayIndex(0),
                actual: Type::Bytes,
            }),
            "[0]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("echo ( http.headers[*][\"host\"] );"),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapKey("host".into()),
                actual: Type::Bytes,
            }),
            "[\"host\"]"
        );

        assert_err!(
            FilterParser::new(&SCHEME)
                .lex_as::<FunctionCallExpr>("echo ( http.host, http.headers[*] );"),
            LexErrorKind::InvalidMapEachAccess,
            "http.headers[*]"
        );
    }
    #[test]
    fn test_indexed_native_function_arguments_materialize_only_the_selection() {
        use crate::native::values::{
            ArrayRead, IntoLhsValue, MapRead, NativeArray, NativeMap, NativeValue,
        };
        use crate::{EvaluationContext, HasScheme, ListMatcher, ListRef};
        use std::cell::{Cell, RefCell};
        use std::collections::BTreeMap;

        struct HeaderValues {
            values: Vec<Box<[u8]>>,
            gets: Cell<usize>,
            iterations: Cell<usize>,
        }
        impl NativeValue for HeaderValues {
            type Read = ArrayRead;
            type ValueType = crate::native::values::Array<crate::native::values::Bytes>;
        }
        impl NativeArray for HeaderValues {
            type Element = crate::native::values::Bytes;
            type Item<'a> = &'a Box<[u8]>;
            type Iter<'a> = std::slice::Iter<'a, Box<[u8]>>;

            fn get(&self, index: usize) -> Option<Self::Item<'_>> {
                self.gets.set(self.gets.get() + 1);
                self.values.get(index)
            }

            fn iter(&self) -> Self::Iter<'_> {
                self.iterations.set(self.iterations.get() + 1);
                self.values.iter()
            }
        }
        struct Headers {
            entries: BTreeMap<Box<[u8]>, HeaderValues>,
            keys: RefCell<Vec<Box<[u8]>>>,
            value_iterations: Cell<usize>,
            entry_iterations: Cell<usize>,
        }
        impl NativeValue for Headers {
            type Read = MapRead;
            type ValueType = crate::native::values::Map<
                crate::native::values::Array<crate::native::values::Bytes>,
            >;
        }
        impl NativeMap for Headers {
            type Element = crate::native::values::Array<crate::native::values::Bytes>;
            type Item<'a> = &'a HeaderValues;
            type Iter<'a> = std::collections::btree_map::Values<'a, Box<[u8]>, HeaderValues>;

            fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
                self.keys.borrow_mut().push(key.into());
                self.entries.get(key)
            }

            fn values(&self) -> Self::Iter<'_> {
                self.value_iterations.set(self.value_iterations.get() + 1);
                self.entries.values()
            }

            fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(&[u8], Self::Item<'a>)) {
                self.entry_iterations.set(self.entry_iterations.get() + 1);
                for (key, value) in &self.entries {
                    visitor(key, value);
                }
            }
        }
        struct Request {
            scheme: Scheme,
            headers: Headers,
        }
        impl HasScheme for Request {
            fn scheme(&self) -> &Scheme {
                &self.scheme
            }
        }
        impl EvaluationContext for Request {
            type UserData = ();

            fn get_user_data(&self) -> &() {
                &()
            }

            fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
                unreachable!()
            }
        }
        crate::wirefilter_fields! {
            impl HeaderFields for Request {
                "http.request.headers" => {
                    fn(request: &Request) -> &Headers { &request.headers }
                },
            }
        }
        fn lower_borrowed<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
            let LhsValue::Bytes(mut value) = args.next()?.ok()? else {
                unreachable!()
            };
            assert!(matches!(value, crate::Bytes::Borrowed(_)));
            if value.iter().any(u8::is_ascii_uppercase) {
                value.to_mut().make_ascii_lowercase();
            }
            Some(value.into())
        }
        let array_type = Type::array(Type::Bytes);
        let map_type = Type::map(array_type);
        let mut builder = crate::SchemeBuilder::new();
        builder.add_field("http.request.headers", map_type).unwrap();
        for (name, val_type, implementation) in [
            (
                "lower",
                Type::Bytes,
                SimpleFunctionImpl::new(lower_borrowed),
            ),
            (
                "echo_array",
                array_type,
                SimpleFunctionImpl::new(echo_function),
            ),
            ("echo_map", map_type, SimpleFunctionImpl::new(echo_function)),
        ] {
            builder
                .add_function(
                    name,
                    SimpleFunctionDefinition {
                        params: Box::new([SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Field,
                            val_type,
                        }]),
                        opt_params: Box::new([]),
                        return_type: val_type,
                        implementation,
                    },
                )
                .unwrap();
        }
        let scheme = builder.build();
        HeaderFields::validate_scheme(&scheme).unwrap();
        let entries: BTreeMap<Box<[u8]>, Vec<Box<[u8]>>> = (0..128)
            .map(|index| {
                (
                    format!("x-bench-{index}").into_bytes().into_boxed_slice(),
                    vec![format!("value-{index}").into_bytes().into_boxed_slice()],
                )
            })
            .collect();
        let request = || Request {
            scheme: scheme.clone(),
            headers: Headers {
                entries: entries
                    .iter()
                    .map(|(key, values)| {
                        (
                            key.clone(),
                            HeaderValues {
                                values: values.clone(),
                                gets: Cell::new(0),
                                iterations: Cell::new(0),
                            },
                        )
                    })
                    .collect(),
                keys: RefCell::new(Vec::new()),
                value_iterations: Cell::new(0),
                entry_iterations: Cell::new(0),
            },
        };
        let mut stored = crate::ExecutionContext::new(&scheme);
        stored
            .set_field_value_from_name("http.request.headers", (&entries).into_lhs())
            .unwrap();
        // Expected accesses per evaluation: key, array lookup, array iteration,
        // and whether the function needs the complete map.
        for (expression, expected, key, array_gets, array_iterations, complete_map) in [
            (
                r#"any(lower(http.request.headers["x-bench-0"][*])[*] eq "value-0")"#,
                true,
                Some(b"x-bench-0".as_slice()),
                0,
                1,
                false,
            ),
            (
                r#"lower(http.request.headers["x-bench-0"][0]) eq "value-0""#,
                true,
                Some(b"x-bench-0".as_slice()),
                1,
                0,
                false,
            ),
            (
                r#"lower(http.request.headers["missing"][0]) eq """#,
                false,
                Some(b"missing".as_slice()),
                0,
                0,
                false,
            ),
            (
                r#"any(lower(http.request.headers["missing"][*])[*] eq "")"#,
                false,
                Some(b"missing".as_slice()),
                0,
                0,
                false,
            ),
            (
                r#"lower(http.request.headers["x-bench-0"][99]) eq """#,
                false,
                Some(b"x-bench-0".as_slice()),
                1,
                0,
                false,
            ),
            (
                r#"any(echo_array(http.request.headers["x-bench-0"])[*] eq "value-0")"#,
                true,
                Some(b"x-bench-0".as_slice()),
                0,
                1,
                false,
            ),
            (
                r#"echo_map(http.request.headers)["x-bench-0"][0] eq "value-0""#,
                true,
                None,
                0,
                1,
                true,
            ),
        ] {
            let native = request();
            let filter = scheme
                .parse(expression)
                .unwrap()
                .compile_with_compiler(&mut crate::DefaultCompiler::<(), HeaderFields>::new());
            let stored_filter = scheme.parse(expression).unwrap().compile();
            for evaluations in 1..=4 {
                assert_eq!(filter.execute(&native).unwrap(), expected, "{expression}");
                assert_eq!(
                    stored_filter.execute(&stored).unwrap(),
                    expected,
                    "{expression}"
                );
                assert_eq!(
                    native.headers.keys.borrow().as_slice(),
                    key.map_or_else(Vec::new, |key| vec![Box::<[u8]>::from(key); evaluations]),
                    "{expression}",
                );
                assert_eq!(
                    native.headers.value_iterations.get(),
                    evaluations * usize::from(complete_map),
                    "{expression}"
                );
                assert_eq!(
                    native.headers.entry_iterations.get(),
                    evaluations * usize::from(complete_map),
                    "{expression}"
                );
                for (name, values) in &native.headers.entries {
                    let selected = name.as_ref() == b"x-bench-0";
                    assert_eq!(
                        values.gets.get(),
                        evaluations * if selected { array_gets } else { 0 },
                        "{expression}: {name:?}"
                    );
                    assert_eq!(
                        values.iterations.get(),
                        evaluations
                            * if selected {
                                array_iterations
                            } else {
                                usize::from(complete_map)
                            },
                        "{expression}: {name:?}"
                    );
                }
            }
        }

        let native = request();
        let filter = scheme
            .parse_value(r#"lower(http.request.headers["x-bench-0"][0])"#)
            .unwrap()
            .compile_with_compiler(&mut crate::DefaultCompiler::<(), HeaderFields>::new());
        let value = filter.execute(&native).unwrap().unwrap();
        let LhsValue::Bytes(crate::Bytes::Borrowed(value)) = value else {
            panic!("selected header payload should remain borrowed");
        };
        assert!(std::ptr::eq(
            value,
            native.headers.entries[b"x-bench-0".as_slice()].values[0].as_ref()
        ));

        for (selection, array_index) in
            [("[*][0]", Some(0)), ("[*][*]", None), ("[*][99]", Some(99))]
        {
            for empty_map in [false, true] {
                let mut native = request();
                if empty_map {
                    native.headers.entries.clear();
                } else {
                    native
                        .headers
                        .entries
                        .get_mut(b"x-bench-1".as_slice())
                        .unwrap()
                        .values
                        .clear();
                    native
                        .headers
                        .entries
                        .get_mut(b"x-bench-2".as_slice())
                        .unwrap()
                        .values
                        .push(b"second-value".as_slice().into());
                }
                let entries: BTreeMap<_, _> = native
                    .headers
                    .entries
                    .iter()
                    .map(|(key, values)| (key.clone(), values.values.clone()))
                    .collect();
                let mut stored = crate::ExecutionContext::new(&scheme);
                stored
                    .set_field_value_from_name("http.request.headers", (&entries).into_lhs())
                    .unwrap();
                let expression = format!("lower(http.request.headers{selection})");
                let filter = scheme
                    .parse_value(&expression)
                    .unwrap()
                    .compile_with_compiler(&mut crate::DefaultCompiler::<(), HeaderFields>::new());
                let stored_filter = scheme.parse_value(&expression).unwrap().compile();
                let expected: Vec<_> = native
                    .headers
                    .entries
                    .values()
                    .flat_map(|values| match array_index {
                        Some(index) => values.values.get(index).into_iter().collect::<Vec<_>>(),
                        None => values.values.iter().collect(),
                    })
                    .collect();

                for evaluations in 1..=4 {
                    let value = filter.execute(&native).unwrap().unwrap();
                    assert_eq!(
                        value,
                        stored_filter.execute(&stored).unwrap().unwrap(),
                        "{expression}"
                    );
                    let LhsValue::Array(values) = value else {
                        panic!("flattened selection should return an array");
                    };
                    assert_eq!(values.len(), expected.len(), "{expression}");
                    for (actual, expected) in values.into_iter().zip(&expected) {
                        let LhsValue::Bytes(crate::Bytes::Borrowed(actual)) = actual else {
                            panic!("selected header payload should remain borrowed");
                        };
                        assert!(std::ptr::eq(actual, expected.as_ref()), "{expression}");
                    }
                    assert!(native.headers.keys.borrow().is_empty(), "{expression}");
                    assert_eq!(
                        native.headers.value_iterations.get(),
                        evaluations,
                        "{expression}"
                    );
                    assert_eq!(native.headers.entry_iterations.get(), 0, "{expression}");
                    for values in native.headers.entries.values() {
                        assert_eq!(
                            values.gets.get(),
                            evaluations * usize::from(array_index.is_some()),
                            "{expression}"
                        );
                        assert_eq!(
                            values.iterations.get(),
                            evaluations * usize::from(array_index.is_none()),
                            "{expression}"
                        );
                    }
                }
            }
        }

        struct PreserveMap<F> {
            argument_hooks: usize,
            index_hooks: usize,
            family: std::marker::PhantomData<F>,
        }
        impl<F> PreserveMap<F> {
            fn new() -> Self {
                Self {
                    argument_hooks: 0,
                    index_hooks: 0,
                    family: std::marker::PhantomData,
                }
            }
        }
        impl<F: crate::ContextFamily<UserData = ()>> crate::Compiler for PreserveMap<F> {
            type Family = F;
            type U = ();

            fn compile_function_call_arg_expr(
                &mut self,
                node: FunctionCallArgExpr,
            ) -> CompiledValueExpr<Self::U, Self::Family> {
                self.argument_hooks += 1;
                let value = self.compile_value_expr(node);
                CompiledValueExpr::new_with_context(move |ctx| {
                    let result = value.execute(ctx.context());
                    assert!(matches!(&result, Ok(LhsValue::Map(_))));
                    result
                })
            }

            fn compile_index_expr(
                &mut self,
                node: IndexExpr,
            ) -> CompiledValueExpr<Self::U, Self::Family> {
                let terminal_map = node.indexes.as_ref() == [FieldIndex::MapEach];
                let value = self.compile_value_expr(node);
                if terminal_map {
                    self.index_hooks += 1;
                    CompiledValueExpr::new_with_context(move |ctx| {
                        let result = value.execute(ctx.context());
                        assert!(matches!(&result, Ok(LhsValue::Map(_))));
                        result
                    })
                } else {
                    value
                }
            }
        }

        // A single terminal `[*]` preserves the map visible to compiler hooks,
        // even though the mapped function consumes only its values.
        for (expression, argument_hooks) in [
            ("echo_array(http.request.headers[*])", 1),
            ("echo_array(echo_map(http.request.headers)[*])", 2),
        ] {
            let mut native_compiler = PreserveMap::<HeaderFields>::new();
            let native_filter = scheme
                .parse_value(expression)
                .unwrap()
                .compile_with_compiler(&mut native_compiler);
            let mut stored_compiler = PreserveMap::<crate::ExecutionContextFamily<()>>::new();
            let stored_filter = scheme
                .parse_value(expression)
                .unwrap()
                .compile_with_compiler(&mut stored_compiler);
            assert_eq!(native_compiler.argument_hooks, argument_hooks);
            assert_eq!(native_compiler.index_hooks, 1);
            assert_eq!(stored_compiler.argument_hooks, argument_hooks);
            assert_eq!(stored_compiler.index_hooks, 1);
            let native = request();
            assert_eq!(
                native_filter.execute(&native).unwrap(),
                stored_filter.execute(&stored).unwrap()
            );
            assert_eq!(native.headers.entry_iterations.get(), 1);
        }
    }

    #[test]
    fn test_mapped_native_extra_arguments_convert_once_and_remain_lazy() {
        use crate::native::values::{IntoLhsValue, MapRead, NativeMap, NativeValue};
        use crate::{EvaluationContext, HasScheme, ListMatcher, ListRef};
        use std::cell::Cell;
        use std::collections::BTreeMap;
        use std::sync::OnceLock;

        struct CountingMap {
            entries: BTreeMap<Box<[u8]>, i64>,
            conversions: Cell<usize>,
        }
        impl NativeValue for CountingMap {
            type Read = MapRead;
            type ValueType = crate::native::values::Map<crate::native::values::Int>;
        }
        impl NativeMap for CountingMap {
            type Element = crate::native::values::Int;
            type Item<'a> = &'a i64;
            type Iter<'a> = std::collections::btree_map::Values<'a, Box<[u8]>, i64>;

            fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
                self.entries.get(key)
            }

            fn values(&self) -> Self::Iter<'_> {
                self.entries.values()
            }

            fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(&[u8], Self::Item<'a>)) {
                self.conversions.set(self.conversions.get() + 1);
                for (key, value) in &self.entries {
                    visitor(key, value);
                }
            }
        }
        struct Request {
            scheme: Scheme,
            numbers: Option<Vec<i64>>,
            number: i64,
            boolean: bool,
            bytes: Box<str>,
            ip: std::net::IpAddr,
            scalar_getters: Cell<usize>,
            map: OnceLock<CountingMap>,
            provide_map: bool,
            map_getters: Cell<usize>,
        }
        impl HasScheme for Request {
            fn scheme(&self) -> &Scheme {
                &self.scheme
            }
        }
        impl EvaluationContext for Request {
            type UserData = ();

            fn get_user_data(&self) -> &() {
                &()
            }

            fn get_list_matcher(&self, _: ListRef<'_>) -> &dyn ListMatcher {
                unreachable!()
            }
        }
        crate::wirefilter_fields! {
            impl NativeFields for Request {
                "numbers" => {
                    fn(request: &Request) -> Option<&Vec<i64>> {
                        request.numbers.as_ref()
                    }
                },
                "number" => {
                    fn(request: &Request) -> i64 {
                        request.scalar_getters.set(request.scalar_getters.get() + 1);
                        request.number
                    }
                },
                "boolean" => {
                    fn(request: &Request) -> bool {
                        request.scalar_getters.set(request.scalar_getters.get() + 1);
                        request.boolean
                    }
                },
                "bytes" => {
                    fn(request: &Request) -> &str {
                        request.scalar_getters.set(request.scalar_getters.get() + 1);
                        &request.bytes
                    }
                },
                "ip" => {
                    fn(request: &Request) -> std::net::IpAddr {
                        request.scalar_getters.set(request.scalar_getters.get() + 1);
                        request.ip
                    }
                },
                "map" => {
                    fn(request: &Request) -> &CountingMap {
                        request.map_getters.set(request.map_getters.get() + 1);
                        assert!(request.provide_map, "mandatory map accessed while unavailable");
                        request.map.get_or_init(|| CountingMap {
                            entries: BTreeMap::from([(Box::from(b"a".as_slice()), 1)]),
                            conversions: Cell::new(0),
                        })
                    }
                },
            }
        }
        fn consume_both<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
            args.next()?.ok()?;
            args.next()?.ok()?;
            Some(true.into())
        }
        fn consume_first<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
            args.next()?.ok()?;
            Some(true.into())
        }
        fn identity<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
            args.next()?.ok()
        }
        let map_type = Type::map(Type::Int);
        let mut builder = crate::SchemeBuilder::new();
        builder
            .add_optional_field("numbers", Type::array(Type::Int))
            .unwrap();
        builder.add_field("map", map_type).unwrap();
        for (name, ty) in [
            ("number", Type::Int),
            ("boolean", Type::Bool),
            ("bytes", Type::Bytes),
            ("ip", Type::Ip),
        ] {
            builder.add_field(name, ty).unwrap();
        }
        for (name, extra, implementation) in [
            ("map_arg", map_type, SimpleFunctionImpl::new(consume_both)),
            ("int_arg", Type::Int, SimpleFunctionImpl::new(consume_both)),
            (
                "bool_arg",
                Type::Bool,
                SimpleFunctionImpl::new(consume_both),
            ),
            (
                "bytes_arg",
                Type::Bytes,
                SimpleFunctionImpl::new(consume_both),
            ),
            ("ip_arg", Type::Ip, SimpleFunctionImpl::new(consume_both)),
            (
                "ignore_map",
                map_type,
                SimpleFunctionImpl::new(consume_first),
            ),
        ] {
            builder
                .add_function(
                    name,
                    SimpleFunctionDefinition {
                        params: Box::new([
                            SimpleFunctionParam {
                                arg_kind: SimpleFunctionArgKind::Field,
                                val_type: Type::Int,
                            },
                            SimpleFunctionParam {
                                arg_kind: SimpleFunctionArgKind::Field,
                                val_type: extra,
                            },
                        ]),
                        opt_params: Box::new([]),
                        return_type: Type::Bool,
                        implementation,
                    },
                )
                .unwrap();
        }
        builder
            .add_function(
                "echo_map",
                SimpleFunctionDefinition {
                    params: Box::new([SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: map_type,
                    }]),
                    opt_params: Box::new([]),
                    return_type: map_type,
                    implementation: SimpleFunctionImpl::new(identity),
                },
            )
            .unwrap();
        let scheme = builder.build();
        NativeFields::validate_scheme(&scheme).unwrap();
        let request = |numbers, provide_map| Request {
            scheme: scheme.clone(),
            numbers,
            number: 1,
            boolean: true,
            bytes: Box::from("value"),
            ip: std::net::Ipv4Addr::LOCALHOST.into(),
            scalar_getters: Cell::new(0),
            map: OnceLock::new(),
            provide_map,
            map_getters: Cell::new(0),
        };
        let compile = |expression| {
            scheme
                .parse(expression)
                .unwrap()
                .compile_with_compiler(&mut crate::DefaultCompiler::<(), NativeFields>::new())
        };

        struct StoredReads;
        impl crate::Compiler for StoredReads {
            type Family = crate::ExecutionContextFamily<Self::U>;
            type U = Cell<usize>;

            fn compile_index_expr(&mut self, node: IndexExpr) -> CompiledValueExpr<Self::U> {
                let track = matches!(&node.identifier, IdentifierExpr::Field(field) if field.name() == "map");
                let value = self.compile_value_expr(node);
                if track {
                    CompiledValueExpr::<Self::U, Self::Family>::new_with_context(move |ctx| {
                        let ctx = ctx.context();
                        let reads = ctx.get_user_data();
                        reads.set(reads.get() + 1);
                        value.execute(ctx)
                    })
                } else {
                    value
                }
            }
        }
        let map = BTreeMap::from([(Box::<[u8]>::from(b"a".as_slice()), 1i64)]);
        for (expression, conversions_per_call) in [
            ("any(map_arg(numbers[*], map))", 1),
            (r#"any(int_arg(numbers[*], map["a"]))"#, 0),
        ] {
            let native = request(Some(vec![1, 2, 3]), true);
            let filter = compile(expression);
            assert!(native.map.get().is_none());
            assert_eq!(native.map_getters.get(), 0);
            for calls in [1, 2] {
                assert!(filter.execute(&native).unwrap());
                assert_eq!(native.map_getters.get(), calls);
                assert_eq!(
                    native.map.get().unwrap().conversions.get(),
                    calls * conversions_per_call
                );
            }
            let stored_filter = scheme
                .parse(expression)
                .unwrap()
                .compile_with_compiler(&mut StoredReads);
            let mut stored = crate::ExecutionContext::new_with(&scheme, || Cell::new(0usize));
            stored
                .set_field_value_from_name(
                    "numbers",
                    Array::try_from_iter(Type::Int, [1i64, 2, 3]).unwrap(),
                )
                .unwrap();
            stored
                .set_field_value_from_name("map", (&map).into_lhs())
                .unwrap();
            assert!(stored_filter.execute(&stored).unwrap());
            assert_eq!(
                stored.get_user_data().get(),
                3,
                "stored fields keep their existing cheap access path"
            );

            for numbers in [Some(Vec::new()), None] {
                for provide_map in [false, true] {
                    let native = request(numbers.clone(), provide_map);
                    assert!(!filter.execute(&native).unwrap());
                    assert_eq!(native.map_getters.get(), 0);
                    assert!(native.map.get().is_none());
                    let mut stored =
                        crate::ExecutionContext::new_with(&scheme, || Cell::new(0usize));
                    if let Some(numbers) = &numbers {
                        stored
                            .set_field_value_from_name(
                                "numbers",
                                Array::try_from_iter(Type::Int, numbers.iter().copied()).unwrap(),
                            )
                            .unwrap();
                    }
                    assert!(!stored_filter.execute(&stored).unwrap());
                    assert_eq!(stored.get_user_data().get(), 0);
                }
            }
        }
        struct CountingBindings<F> {
            fields: BTreeMap<Box<str>, usize>,
            family: std::marker::PhantomData<fn() -> F>,
        }
        impl<F> CountingBindings<F> {
            fn new() -> Self {
                Self {
                    fields: BTreeMap::new(),
                    family: std::marker::PhantomData,
                }
            }
        }
        impl<F: crate::ContextFamily> crate::Compiler for CountingBindings<F> {
            type Family = F;
            type U = F::UserData;

            fn bind_field<B: crate::FieldConsumer<F>>(
                &mut self,
                field: crate::Field,
                consumer: B,
            ) -> Result<B::Output, crate::FieldBindingError> {
                *self.fields.entry(field.name().into()).or_default() += 1;
                F::bind(field, consumer)
            }
        }
        // Scalar roots only bind for value compilation. Indexed collection roots
        // still need classification, even though the argument itself is scalar.
        for (expression, extra_field, bindings, scalar_getters) in [
            ("any(int_arg(numbers[*], number))", "number", 1, 3),
            ("any(bool_arg(numbers[*], boolean))", "boolean", 1, 3),
            ("any(bytes_arg(numbers[*], bytes))", "bytes", 1, 3),
            ("any(ip_arg(numbers[*], ip))", "ip", 1, 3),
            (r#"any(int_arg(numbers[*], map["a"]))"#, "map", 2, 0),
            // The mapped argument contributes the third binding of numbers.
            ("any(int_arg(numbers[*], numbers[0]))", "numbers", 3, 0),
        ] {
            let native = request(Some(vec![1, 2, 3]), true);
            let mut native_compiler = CountingBindings::<NativeFields>::new();
            let native_filter = scheme
                .parse(expression)
                .unwrap()
                .compile_with_compiler(&mut native_compiler);
            assert_eq!(
                native_compiler.fields[extra_field], bindings,
                "{expression}"
            );
            assert_eq!(native.scalar_getters.get(), 0);
            let native_bindings = native_compiler.fields.clone();

            let mut stored_compiler = CountingBindings::<crate::ExecutionContextFamily<()>>::new();
            let stored_filter = scheme
                .parse(expression)
                .unwrap()
                .compile_with_compiler(&mut stored_compiler);
            assert_eq!(
                stored_compiler.fields[extra_field], bindings,
                "{expression}"
            );
            let stored_bindings = stored_compiler.fields.clone();
            let mut stored = crate::ExecutionContext::new(&scheme);
            stored
                .set_field_value_from_name(
                    "numbers",
                    Array::try_from_iter(Type::Int, [1i64, 2, 3]).unwrap(),
                )
                .unwrap();
            for (name, value) in [
                ("number", native.number.into()),
                ("boolean", native.boolean.into()),
                ("bytes", native.bytes.as_bytes().into()),
                ("ip", native.ip.into()),
                ("map", (&map).into_lhs()),
            ] {
                stored.set_field_value_from_name(name, value).unwrap();
            }
            for calls in [1, 2] {
                assert!(native_filter.execute(&native).unwrap(), "{expression}");
                assert!(stored_filter.execute(&stored).unwrap(), "{expression}");
                assert_eq!(native.scalar_getters.get(), calls * scalar_getters);
                assert_eq!(native_compiler.fields, native_bindings);
                assert_eq!(stored_compiler.fields, stored_bindings);
            }
        }
        // FunctionArgs may leave an extra argument unconsumed even when a mapped
        // call runs. Its mandatory field must remain unread in that case.
        let ignored = request(Some(vec![1, 2, 3]), false);
        assert!(
            compile("any(ignore_map(numbers[*], map))")
                .execute(&ignored)
                .unwrap()
        );
        assert_eq!(ignored.map_getters.get(), 0);
        assert!(ignored.map.get().is_none());

        // Preserve the established eager handling for an existing expensive
        // function argument, including when the mapped input is empty.
        let eager_expression = "any(map_arg(numbers[*], echo_map(map)))";
        let empty = request(Some(Vec::new()), true);
        assert!(!compile(eager_expression).execute(&empty).unwrap());
        assert_eq!(empty.map_getters.get(), 1);
        assert_eq!(empty.map.get().unwrap().conversions.get(), 1);
        let mut stored = crate::ExecutionContext::new_with(&scheme, || Cell::new(0usize));
        stored
            .set_field_value_from_name("numbers", Array::new(Type::Int))
            .unwrap();
        stored
            .set_field_value_from_name("map", (&map).into_lhs())
            .unwrap();
        assert!(
            !scheme
                .parse(eager_expression)
                .unwrap()
                .compile_with_compiler(&mut StoredReads)
                .execute(&stored)
                .unwrap()
        );
        assert_eq!(stored.get_user_data().get(), 1);
    }
}
