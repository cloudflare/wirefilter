use super::Expr;
use super::function_expr::FunctionCallExpr;
use super::parse::FilterParser;
use super::visitor::{Visitor, VisitorMut};
use crate::ast::index_expr::{Compare, IndexExpr};
use crate::compiler::Compiler;
use crate::filter::{CompiledExpr, CompiledOneExpr, CompiledVecExpr};
use crate::lex::{Lex, LexErrorKind, LexResult, LexWith, expect, skip_space, span};
use crate::lhs_types::TypedArray;
use crate::range_set::RangeSet;
use crate::rhs_types::{BytesExpr, ExplicitIpRange, ListName, Regex, Wildcard};
use crate::scheme::{Field, Identifier, List};
use crate::searcher::{EmptySearcher, MemmemSearcher};
use crate::strict_partial_ord::StrictPartialOrd;
use crate::types::{
    ExpectedTypeList, GetType, LhsValue, LiteralSet, LiteralValue, Type, TypeMismatchError,
};
use crate::{ExecutionContext, Scheme};
use serde::{Serialize, Serializer};
use sliceslice::MemchrSearcher;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
#[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "wasm32"))]
use std::sync::LazyLock;

const LESS: u8 = 0b001;
const GREATER: u8 = 0b010;
const EQUAL: u8 = 0b100;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
static USE_AVX2: LazyLock<bool> = LazyLock::new(|| {
    use std::env;

    const NO_VALUES: &[&str] = &["0", "no", "false"];

    let use_avx2 = env::var("WIREFILTER_USE_AVX2").unwrap_or_default();
    is_x86_feature_detected!("avx2") && !NO_VALUES.contains(&use_avx2.as_str())
});

#[cfg(target_arch = "wasm32")]
static USE_SIMD128: LazyLock<bool> = LazyLock::new(|| {
    use std::env;

    const NO_VALUES: &[&str] = &["0", "no", "false"];

    let use_simd128 = env::var("WIREFILTER_USE_SIMD128").unwrap_or_default();
    !NO_VALUES.contains(&use_simd128.as_str())
});

lex_enum!(
    /// OrderingOp is an operator for an ordering [`ComparisonOpExpr`].
    #[repr(u8)] OrderingOp {
        /// `eq` / `==` operator
        "eq" | "==" => Equal = EQUAL,
        /// `ne` / `!=` operator
        "ne" | "!=" => NotEqual = LESS | GREATER,
        /// `ge` / `>=` operator
        "ge" | ">=" => GreaterThanEqual = GREATER | EQUAL,
        /// `le` / `<=` operator
        "le" | "<=" => LessThanEqual = LESS | EQUAL,
        /// `gt` / `>` operator
        "gt" | ">" => GreaterThan = GREATER,
        /// `lt` / `<` operator
        "lt" | "<" => LessThan = LESS,
    }
);

impl OrderingOp {
    /// Determines whether the operator matches a given ordering.
    #[inline]
    pub fn matches(self, ordering: Ordering) -> bool {
        let mask = self as u8;
        let flag = match ordering {
            Ordering::Less => LESS,
            Ordering::Greater => GREATER,
            Ordering::Equal => EQUAL,
        };
        mask & flag != 0
    }

    /// Same as `matches` but accepts an optional ordering for incomparable
    /// types.
    #[inline]
    pub fn matches_opt(self, ordering: Option<Ordering>) -> bool {
        match ordering {
            Some(ordering) => self.matches(ordering),
            // only `!=` should be true for incomparable types
            None => self == OrderingOp::NotEqual,
        }
    }
}

lex_enum!(
    /// An integer operator
    IntOp {
        /// `bitwise_and` / `&` operator
        "&" | "bitwise_and" => BitwiseAnd,
    }
);

lex_enum!(BytesOp {
    "contains" => Contains,
    "~" | "matches" => Matches,
    "wildcard" => Wildcard,
    "strict wildcard" => StrictWildcard,
});

lex_enum!(ComparisonOp {
    "in" => In,
    OrderingOp => Ordering,
    IntOp => Int,
    BytesOp => Bytes,
});

/// A scalar byte, integer, or IP expression backed by an [`IndexExpr`].
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ScalarExpr(IndexExpr);

impl ScalarExpr {
    /// Returns the underlying indexed expression.
    pub fn as_index_expr(&self) -> &IndexExpr {
        &self.0
    }

    /// Consumes this expression and returns the underlying indexed expression.
    pub fn into_index_expr(self) -> IndexExpr {
        self.0
    }

    pub(crate) fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        super::ValueExpr::walk_mut(&mut self.0, visitor);
    }
}

impl TryFrom<IndexExpr> for ScalarExpr {
    type Error = TypeMismatchError;

    fn try_from(expr: IndexExpr) -> Result<Self, Self::Error> {
        let actual = expr.output_type();
        if matches!(actual, Type::Bytes | Type::Int | Type::Ip) {
            Ok(Self(expr))
        } else {
            let mut expected = ExpectedTypeList::default();
            expected.insert(Type::Bytes);
            expected.insert(Type::Int);
            expected.insert(Type::Ip);
            Err(TypeMismatchError { expected, actual })
        }
    }
}

impl From<ScalarExpr> for IndexExpr {
    fn from(expr: ScalarExpr) -> Self {
        expr.into_index_expr()
    }
}

impl GetType for ScalarExpr {
    fn get_type(&self) -> Type {
        self.0.get_type()
    }
}

impl Serialize for ScalarExpr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

/// A scalar integer expression backed by an [`IndexExpr`].
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ScalarIntExpr(ScalarExpr);

impl ScalarIntExpr {
    /// Returns the underlying indexed expression.
    pub fn as_index_expr(&self) -> &IndexExpr {
        self.0.as_index_expr()
    }

    /// Consumes this expression and returns the underlying indexed expression.
    pub fn into_index_expr(self) -> IndexExpr {
        self.0.into_index_expr()
    }

    pub(crate) fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        self.0.walk_mut(visitor);
    }
}

impl TryFrom<IndexExpr> for ScalarIntExpr {
    type Error = TypeMismatchError;

    fn try_from(expr: IndexExpr) -> Result<Self, Self::Error> {
        let actual = expr.output_type();
        if actual == Type::Int {
            Ok(Self(ScalarExpr(expr)))
        } else {
            Err(TypeMismatchError {
                expected: Type::Int.into(),
                actual,
            })
        }
    }
}

impl From<ScalarIntExpr> for ScalarExpr {
    fn from(expr: ScalarIntExpr) -> Self {
        expr.0
    }
}

impl TryFrom<ScalarExpr> for ScalarIntExpr {
    type Error = TypeMismatchError;

    fn try_from(expr: ScalarExpr) -> Result<Self, Self::Error> {
        let actual = expr.get_type();
        if actual == Type::Int {
            Ok(Self(expr))
        } else {
            Err(TypeMismatchError {
                expected: Type::Int.into(),
                actual,
            })
        }
    }
}

impl From<ScalarIntExpr> for IndexExpr {
    fn from(expr: ScalarIntExpr) -> Self {
        expr.into_index_expr()
    }
}

impl GetType for ScalarIntExpr {
    fn get_type(&self) -> Type {
        Type::Int
    }
}

impl Serialize for ScalarIntExpr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

/// A right-hand side operand of an integer-specific comparison.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum IntRhs {
    /// An integer literal.
    Literal(i64),
    /// A dynamically evaluated scalar integer expression.
    Index(ScalarIntExpr),
}

impl GetType for IntRhs {
    fn get_type(&self) -> Type {
        Type::Int
    }
}

fn serialize_index_expr_operand<S: Serializer>(
    expr: &IndexExpr,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;

    let mut out = serializer.serialize_struct("ComparisonRhs", 2)?;
    out.serialize_field("kind", "IndexExpr")?;
    out.serialize_field("value", expr)?;
    out.end()
}

impl Serialize for IntRhs {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Literal(value) => value.serialize(serializer),
            Self::Index(expr) => serialize_index_expr_operand(expr.as_index_expr(), serializer),
        }
    }
}

/// A right-hand side operand of an ordering comparison.
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum ComparisonRhs {
    /// A literal operand.
    Literal(LiteralValue),
    /// A dynamically evaluated indexed expression.
    Index(ScalarExpr),
}

impl From<LiteralValue> for ComparisonRhs {
    fn from(value: LiteralValue) -> Self {
        Self::Literal(value)
    }
}

impl From<ScalarIntExpr> for ComparisonRhs {
    fn from(expr: ScalarIntExpr) -> Self {
        Self::Index(expr.into())
    }
}

impl From<ScalarExpr> for ComparisonRhs {
    fn from(expr: ScalarExpr) -> Self {
        Self::Index(expr)
    }
}

impl GetType for ComparisonRhs {
    fn get_type(&self) -> Type {
        match self {
            Self::Literal(value) => value.get_type(),
            Self::Index(expr) => expr.get_type(),
        }
    }
}

impl Serialize for ComparisonRhs {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Literal(value) => value.serialize(serializer),
            Self::Index(expr) => serialize_index_expr_operand(expr.as_index_expr(), serializer),
        }
    }
}

impl ComparisonRhs {
    fn lex_int<'i>(input: &'i str, parser: &FilterParser<'_>) -> LexResult<'i, Self> {
        IntRhs::lex(input, parser).map(|(rhs, rest)| {
            let rhs = match rhs {
                IntRhs::Literal(value) => Self::Literal(LiteralValue::Int(value)),
                IntRhs::Index(expr) => Self::Index(expr.into()),
            };
            (rhs, rest)
        })
    }

    fn lex_typed<'i>(
        input: &'i str,
        parser: &FilterParser<'_>,
        expected: Type,
    ) -> LexResult<'i, Self> {
        match LiteralValue::lex_with(input, expected) {
            Ok((value, rest)) => return Ok((Self::Literal(value), rest)),
            Err(error)
                if !input
                    .as_bytes()
                    .first()
                    .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_') =>
            {
                return Err(error);
            }
            Err(_) => {}
        }

        let (expr, rest) = IndexExpr::lex_with(input, parser)?;

        let actual = expr.output_type();
        if actual == expected {
            Ok((Self::Index(ScalarExpr(expr)), rest))
        } else {
            Err((
                LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: expected.into(),
                    actual,
                }),
                span(input, rest),
            ))
        }
    }

    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        if let Self::Index(expr) = self {
            visitor.visit_scalar_expr(expr);
        }
    }

    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        if let Self::Index(expr) = self {
            visitor.visit_scalar_expr(expr);
        }
    }
}

impl IntRhs {
    fn lex<'i>(input: &'i str, parser: &FilterParser<'_>) -> LexResult<'i, Self> {
        if !input
            .as_bytes()
            .first()
            .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_')
        {
            return i64::lex(input).map(|(value, rest)| (Self::Literal(value), rest));
        }

        let (expr, rest) = IndexExpr::lex_with(input, parser)?;
        ScalarIntExpr::try_from(expr)
            .map(|expr| (Self::Index(expr), rest))
            .map_err(|mismatch| (LexErrorKind::TypeMismatch(mismatch), span(input, rest)))
    }
}

/// Operator and right-hand side expression of a
/// comparison expression.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum ComparisonOpExpr {
    /// Boolean field verification
    #[serde(serialize_with = "serialize_is_true")]
    IsTrue,

    /// Ordering comparison
    Ordering {
        /// Ordering comparison operator:
        /// * "eq" | "=="
        /// * "ne" | "!="
        /// * "ge" | ">="
        /// * "le" | "<="
        /// * "gt" | ">"
        /// * "lt" | "<"
        op: OrderingOp,
        /// Right-hand side operand
        rhs: ComparisonRhs,
    },

    /// Integer comparison
    Int {
        /// Integer comparison operator:
        /// * "&" | "bitwise_and"
        op: IntOp,
        /// Right-hand side integer operand
        rhs: IntRhs,
    },

    /// "contains" comparison
    #[serde(serialize_with = "serialize_contains")]
    Contains(BytesExpr),

    /// "matches / ~" comparison
    #[serde(serialize_with = "serialize_matches")]
    Matches(Regex),

    /// "wildcard" comparison
    #[serde(serialize_with = "serialize_wildcard")]
    Wildcard(Wildcard<false>),

    /// "strict wildcard" comparison
    #[serde(serialize_with = "serialize_strict_wildcard")]
    StrictWildcard(Wildcard<true>),

    /// "in {...}" comparison
    #[serde(serialize_with = "serialize_one_of")]
    OneOf(LiteralSet),

    /// "contains {...}" comparison
    #[serde(serialize_with = "serialize_contains_one_of")]
    ContainsOneOf(Vec<BytesExpr>),

    /// "in $..." comparison
    #[serde(serialize_with = "serialize_list")]
    InList {
        /// `List` from the `Scheme`
        list: List,
        /// List name
        name: ListName,
    },
}

fn serialize_op_rhs<T, S>(op: &'static str, rhs: &T, ser: S) -> Result<S::Ok, S::Error>
where
    T: Serialize + ?Sized,
    S: Serializer,
{
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("ComparisonOpExpr", 2)?;
    out.serialize_field("op", op)?;
    out.serialize_field("rhs", rhs)?;
    out.end()
}

fn serialize_is_true<S: Serializer>(ser: S) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("ComparisonOpExpr", 1)?;
    out.serialize_field("op", "IsTrue")?;
    out.end()
}

fn serialize_contains<S: Serializer>(rhs: &BytesExpr, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Contains", rhs, ser)
}

fn serialize_matches<S: Serializer>(rhs: &Regex, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Matches", rhs, ser)
}

fn serialize_wildcard<S: Serializer>(rhs: &Wildcard<false>, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Wildcard", rhs, ser)
}

fn serialize_strict_wildcard<S: Serializer>(
    rhs: &Wildcard<true>,
    ser: S,
) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Strict Wildcard", rhs, ser)
}

fn serialize_one_of<S: Serializer>(rhs: &LiteralSet, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("OneOf", rhs, ser)
}

fn serialize_contains_one_of<S: Serializer>(rhs: &[BytesExpr], ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("ContainsOneOf", rhs, ser)
}

fn serialize_list<S: Serializer>(_: &List, name: &ListName, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("InList", name, ser)
}

/// Represents either the access to a field's value or
/// a function call.
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(untagged)]
pub enum IdentifierExpr {
    /// Field access
    Field(Field),
    /// Function call
    FunctionCallExpr(FunctionCallExpr),
}

impl IdentifierExpr {
    #[inline]
    fn scheme(&self) -> &Scheme {
        match self {
            Self::Field(f) => f.scheme(),
            Self::FunctionCallExpr(call) => call.function.scheme(),
        }
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for IdentifierExpr {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        let (item, input) = Identifier::lex_with(input, parser.scheme)?;
        match item {
            Identifier::Field(field) => Ok((IdentifierExpr::Field(field.to_owned()), input)),
            Identifier::Function(function) => {
                let nested_parser = parser.with_increased_nesting(skip_space(input))?;
                FunctionCallExpr::lex_with_function(input, &nested_parser, function)
                    .map(|(call, input)| (IdentifierExpr::FunctionCallExpr(call), input))
            }
        }
    }
}

impl GetType for IdentifierExpr {
    fn get_type(&self) -> Type {
        match self {
            IdentifierExpr::Field(field) => field.get_type(),
            IdentifierExpr::FunctionCallExpr(call) => call.get_type(),
        }
    }
}

/// Comparison expression
#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
pub struct ComparisonExpr {
    /// Left-hand side of the comparison expression
    pub lhs: IndexExpr,

    /// Operator + right-hand side of the comparison expression
    #[serde(flatten)]
    pub op: ComparisonOpExpr,
}

impl GetType for ComparisonExpr {
    fn get_type(&self) -> Type {
        if self.lhs.map_each_count() > 0 {
            Type::Array(Type::Bool.into())
        } else if self.op == ComparisonOpExpr::IsTrue {
            // Bool or Array(Bool)
            self.lhs.get_type()
        } else {
            Type::Bool
        }
    }
}

impl<'i> LexWith<'i, &FilterParser<'_>> for ComparisonExpr {
    fn lex_with(input: &'i str, parser: &FilterParser<'_>) -> LexResult<'i, Self> {
        let (lhs, input) = IndexExpr::lex_with(input, parser)?;

        Self::lex_with_lhs(input, parser, lhs)
    }
}

impl ComparisonExpr {
    pub(crate) fn lex_with_lhs<'i>(
        input: &'i str,
        parser: &FilterParser<'_>,
        lhs: IndexExpr,
    ) -> LexResult<'i, Self> {
        let lhs_type = lhs.get_type();

        let (op, input) = if lhs_type == Type::Bool {
            (ComparisonOpExpr::IsTrue, input)
        } else if lhs_type.next() == Some(Type::Bool) {
            // Invalid because this would produce an Array(Array(Bool))
            // which cannot be coerced to an Array(Bool)
            if lhs.map_each_count() > 0 {
                return Err((
                    LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Array(Type::Array(Type::Bool.into()).into()),
                    },
                    span(input, input),
                ));
            } else {
                (ComparisonOpExpr::IsTrue, input)
            }
        } else {
            let initial_input = skip_space(input);
            let (op, input) = ComparisonOp::lex(initial_input)?;

            let input_after_op = input;

            let input = skip_space(input);

            match (&lhs_type, op) {
                (Type::Ip, ComparisonOp::In)
                | (Type::Bytes, ComparisonOp::In)
                | (Type::Int, ComparisonOp::In) => {
                    if expect(input, "$").is_ok() {
                        let (name, input) = ListName::lex(input)?;
                        let list = parser.scheme.get_list(&lhs_type).ok_or((
                            LexErrorKind::UnsupportedOp { lhs_type },
                            span(initial_input, input),
                        ))?;
                        (
                            ComparisonOpExpr::InList {
                                name,
                                list: list.to_owned(),
                            },
                            input,
                        )
                    } else {
                        let (rhs, input) = LiteralSet::lex_with(input, lhs_type)?;
                        (ComparisonOpExpr::OneOf(rhs), input)
                    }
                }
                (Type::Ip, ComparisonOp::Ordering(op))
                | (Type::Bytes, ComparisonOp::Ordering(op)) => {
                    let (rhs, input) = ComparisonRhs::lex_typed(input, parser, lhs_type)?;
                    (ComparisonOpExpr::Ordering { op, rhs }, input)
                }
                (Type::Int, ComparisonOp::Ordering(op)) => {
                    let (rhs, input) = ComparisonRhs::lex_int(input, parser)?;
                    (ComparisonOpExpr::Ordering { op, rhs }, input)
                }
                (Type::Int, ComparisonOp::Int(op)) => {
                    let (rhs, input) = IntRhs::lex(input, parser)?;
                    (ComparisonOpExpr::Int { op, rhs }, input)
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                    BytesOp::Contains => {
                        let (bytes, input) = BytesExpr::lex(input)?;
                        (ComparisonOpExpr::Contains(bytes), input)
                    }
                    BytesOp::Matches => {
                        let (regex, input) = Regex::lex_with(input, parser)?;
                        (ComparisonOpExpr::Matches(regex), input)
                    }
                    BytesOp::Wildcard => {
                        let (wildcard, input) = Wildcard::lex_with(input, parser)?;
                        (ComparisonOpExpr::Wildcard(wildcard), input)
                    }
                    BytesOp::StrictWildcard => {
                        let (wildcard, input) = Wildcard::lex_with(input, parser)?;
                        (ComparisonOpExpr::StrictWildcard(wildcard), input)
                    }
                },
                _ => {
                    return Err((
                        LexErrorKind::UnsupportedOp { lhs_type },
                        span(initial_input, input_after_op),
                    ));
                }
            }
        };

        Ok((ComparisonExpr { lhs, op }, input))
    }

    /// Retrieves the associated left hand side expression.
    pub fn lhs_expr(&self) -> &IndexExpr {
        &self.lhs
    }

    /// Retrieves the operator applied to the left hand side expression.
    pub fn operator(&self) -> &ComparisonOpExpr {
        &self.op
    }
}

macro_rules! cast_value {
    ($value:expr, $ty:ident) => {
        match $value {
            LhsValue::$ty(value) => value,
            _ => unreachable!(),
        }
    };
}

impl<const STRICT: bool, U> Compare<U> for Wildcard<STRICT> {
    #[inline]
    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
        self.is_match(cast_value!(value, Bytes))
    }
}

fn compile_dynamic_comparison<C, F>(
    lhs: IndexExpr,
    rhs: IndexExpr,
    compare: F,
    missing_lhs_default: bool,
    compiler: &mut C,
) -> CompiledExpr<C::U>
where
    C: Compiler,
    F: for<'l, 'r> Fn(&LhsValue<'l>, &LhsValue<'r>) -> bool + Copy + Send + Sync + 'static,
{
    let lhs_is_mapped = lhs.map_each_count() > 0;
    let lhs = compiler.compile_index_expr(lhs);
    let rhs = compiler.compile_index_expr(rhs);

    if lhs_is_mapped {
        CompiledExpr::Vec(CompiledVecExpr::new(move |ctx| {
            let Ok(LhsValue::Array(lhs)) = lhs.execute(ctx) else {
                return TypedArray::default();
            };

            match rhs.execute(ctx) {
                Ok(rhs) => TypedArray::from_iter(lhs.into_iter().map(|lhs| compare(&lhs, &rhs))),
                _ => TypedArray::from_iter(lhs.into_iter().map(|_| false)),
            }
        }))
    } else {
        CompiledExpr::One(CompiledOneExpr::new(move |ctx| {
            match (lhs.execute(ctx), rhs.execute(ctx)) {
                (Ok(lhs), Ok(rhs)) => compare(&lhs, &rhs),
                (Err(_), Ok(_)) => missing_lhs_default,
                _ => false,
            }
        }))
    }
}

impl Expr for ComparisonExpr {
    #[inline]
    fn walk<'a, V: Visitor<'a>>(&'a self, visitor: &mut V) {
        visitor.visit_index_expr(&self.lhs);
        match &self.op {
            ComparisonOpExpr::Ordering { rhs, .. } => rhs.walk(visitor),
            ComparisonOpExpr::Int {
                rhs: IntRhs::Index(rhs),
                ..
            } => visitor.visit_scalar_int_expr(rhs),
            _ => {}
        }
    }

    #[inline]
    fn walk_mut<'a, V: VisitorMut<'a>>(&'a mut self, visitor: &mut V) {
        visitor.visit_index_expr(&mut self.lhs);
        match &mut self.op {
            ComparisonOpExpr::Ordering { rhs, .. } => rhs.walk_mut(visitor),
            ComparisonOpExpr::Int {
                rhs: IntRhs::Index(rhs),
                ..
            } => visitor.visit_scalar_int_expr(rhs),
            _ => {}
        }
    }

    fn compile_with_compiler<C: Compiler>(self, compiler: &mut C) -> CompiledExpr<C::U> {
        let lhs = self.lhs;
        let nil_not_equal_behavior = lhs.identifier.scheme().nil_not_equal_behavior();

        match self.op {
            ComparisonOpExpr::IsTrue => {
                struct IsTrue;

                impl<U> Compare<U> for IsTrue {
                    #[inline]
                    fn compare<'e>(
                        &self,
                        value: &LhsValue<'e>,
                        _: &'e ExecutionContext<'e, U>,
                    ) -> bool {
                        *cast_value!(value, Bool)
                    }
                }

                if lhs.get_type() == Type::Bool {
                    lhs.compile_with(compiler, false, IsTrue)
                } else if lhs.get_type().next() == Some(Type::Bool) {
                    // MapEach is impossible in this case, thus call `compile_vec_with` directly
                    // to coerce LhsValue to Vec<bool>
                    CompiledExpr::Vec(lhs.compile_vec_with(compiler, IsTrue))
                } else {
                    unreachable!()
                }
            }
            ComparisonOpExpr::Ordering { op, rhs } => {
                let rhs = match rhs {
                    ComparisonRhs::Literal(rhs) => rhs,
                    ComparisonRhs::Index(rhs) => {
                        let missing_lhs_default =
                            op == OrderingOp::NotEqual && nil_not_equal_behavior;
                        let rhs_type = rhs.get_type();
                        let rhs = rhs.into();
                        return match rhs_type {
                            Type::Bytes => compile_dynamic_comparison(
                                lhs,
                                rhs,
                                move |lhs, rhs| {
                                    op.matches(
                                        cast_value!(lhs, Bytes)
                                            .as_ref()
                                            .cmp(cast_value!(rhs, Bytes).as_ref()),
                                    )
                                },
                                missing_lhs_default,
                                compiler,
                            ),
                            Type::Int => compile_dynamic_comparison(
                                lhs,
                                rhs,
                                move |lhs, rhs| {
                                    op.matches(cast_value!(lhs, Int).cmp(cast_value!(rhs, Int)))
                                },
                                missing_lhs_default,
                                compiler,
                            ),
                            Type::Ip => compile_dynamic_comparison(
                                lhs,
                                rhs,
                                move |lhs, rhs| {
                                    op.matches_opt(
                                        cast_value!(lhs, Ip)
                                            .strict_partial_cmp(cast_value!(rhs, Ip)),
                                    )
                                },
                                missing_lhs_default,
                                compiler,
                            ),
                            _ => unreachable!(),
                        };
                    }
                };

                macro_rules! gen_ordering {
                    ($op:tt, $def:ident) => {
                        match rhs {
                            LiteralValue::Bytes(bytes) => {
                                struct BytesOp(BytesExpr);

                                impl<U> Compare<U> for BytesOp {
                                    #[inline]
                                    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
                                        cast_value!(value, Bytes).as_ref() $op self.0.as_ref()
                                    }
                                }

                                lhs.compile_with(compiler, $def, BytesOp(bytes))
                            }
                            LiteralValue::Int(int) => {
                                struct IntOp(i64);

                                impl<U> Compare<U> for IntOp {
                                    #[inline]
                                    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
                                        *cast_value!(value, Int) $op self.0
                                    }
                                }

                                lhs.compile_with(compiler, $def, IntOp(int))
                            }
                            LiteralValue::Ip(ip) => {
                                struct IpOp {
                                    op: OrderingOp,
                                    ip: IpAddr,
                                }

                                impl<U> Compare<U> for IpOp {
                                    #[inline]
                                    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
                                        self.op.matches_opt(cast_value!(value, Ip).strict_partial_cmp(&self.ip))
                                    }
                                }

                                lhs.compile_with(compiler, $def, IpOp { op, ip })
                            }
                            LiteralValue::Bool(_) | LiteralValue::Array(_) | LiteralValue::Map(_) => unreachable!(),
                        }
                    };
                }

                match op {
                    OrderingOp::NotEqual => gen_ordering!(!=, nil_not_equal_behavior),
                    OrderingOp::Equal => gen_ordering!(==, false),
                    OrderingOp::GreaterThanEqual => gen_ordering!(>=, false),
                    OrderingOp::LessThanEqual => gen_ordering!(<=, false),
                    OrderingOp::GreaterThan => gen_ordering!(>, false),
                    OrderingOp::LessThan => gen_ordering!(<, false),
                }
            }
            ComparisonOpExpr::Int {
                op: IntOp::BitwiseAnd,
                rhs,
            } => {
                let rhs = match rhs {
                    IntRhs::Literal(rhs) => rhs,
                    IntRhs::Index(rhs) => {
                        return compile_dynamic_comparison(
                            lhs,
                            rhs.into(),
                            |lhs, rhs| cast_value!(lhs, Int) & cast_value!(rhs, Int) != 0,
                            false,
                            compiler,
                        );
                    }
                };

                struct BitwiseAnd(i64);

                impl<U> Compare<U> for BitwiseAnd {
                    #[inline]
                    fn compare<'e>(
                        &self,
                        value: &LhsValue<'e>,
                        _: &'e ExecutionContext<'e, U>,
                    ) -> bool {
                        cast_value!(value, Int) & self.0 != 0
                    }
                }
                lhs.compile_with(compiler, false, BitwiseAnd(rhs))
            }
            ComparisonOpExpr::Contains(bytes) => {
                macro_rules! search {
                    ($searcher:expr) => {{ lhs.compile_with(compiler, false, $searcher) }};
                }

                let bytes: Box<[u8]> = bytes.into();

                if bytes.is_empty() {
                    return search!(EmptySearcher);
                }

                if let [byte] = *bytes {
                    return search!(MemchrSearcher::new(byte));
                }

                #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
                if *USE_AVX2 {
                    use rand::{RngExt, rng};
                    use sliceslice::x86::*;

                    struct ArraySearcher<const N: usize>(Avx2Searcher<[u8; N]>);

                    impl<const N: usize, U> Compare<U> for ArraySearcher<N> {
                        #[inline]
                        fn compare<'e>(
                            &self,
                            value: &LhsValue<'e>,
                            _: &'e ExecutionContext<'e, U>,
                        ) -> bool {
                            unsafe { self.0.search_in(cast_value!(value, Bytes)) }
                        }
                    }

                    struct BoxSearcher(Avx2Searcher<Box<[u8]>>);

                    impl<U> Compare<U> for BoxSearcher {
                        #[inline]
                        fn compare<'e>(
                            &self,
                            value: &LhsValue<'e>,
                            _: &'e ExecutionContext<'e, U>,
                        ) -> bool {
                            unsafe { self.0.search_in(cast_value!(value, Bytes)) }
                        }
                    }

                    fn slice_to_array<const N: usize>(slice: &[u8]) -> [u8; N] {
                        let mut array = [0u8; N];
                        array.copy_from_slice(slice);
                        array
                    }

                    let position = rng().random_range(1..bytes.len());
                    return unsafe {
                        match bytes.len() {
                            2 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<2>(&bytes),
                                position
                            ))),
                            3 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<3>(&bytes),
                                position
                            ))),
                            4 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<4>(&bytes),
                                position
                            ))),
                            5 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<5>(&bytes),
                                position
                            ))),
                            6 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<6>(&bytes),
                                position
                            ))),
                            7 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<7>(&bytes),
                                position
                            ))),
                            8 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<8>(&bytes),
                                position
                            ))),
                            9 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<9>(&bytes),
                                position
                            ))),
                            10 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<10>(&bytes),
                                position
                            ))),
                            11 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<11>(&bytes),
                                position
                            ))),
                            12 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<12>(&bytes),
                                position
                            ))),
                            13 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<13>(&bytes),
                                position
                            ))),
                            14 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<14>(&bytes),
                                position
                            ))),
                            15 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<15>(&bytes),
                                position
                            ))),
                            16 => search!(ArraySearcher(Avx2Searcher::with_position(
                                slice_to_array::<16>(&bytes),
                                position
                            ))),
                            _ => search!(BoxSearcher(Avx2Searcher::with_position(bytes, position))),
                        }
                    };
                }
                #[cfg(target_arch = "wasm32")]
                if *USE_SIMD128 {
                    use rand::{RngExt, rng};
                    use sliceslice::wasm32::*;

                    struct WasmSearcher(Wasm32Searcher<Box<[u8]>>);

                    impl<U> Compare<U> for WasmSearcher {
                        #[inline]
                        fn compare<'e>(
                            &self,
                            value: &LhsValue<'e>,
                            _: &'e ExecutionContext<'e, U>,
                        ) -> bool {
                            unsafe { self.0.search_in(cast_value!(value, Bytes)) }
                        }
                    }

                    let position = rng().random_range(1..bytes.len());

                    return unsafe {
                        search!(WasmSearcher(Wasm32Searcher::with_position(bytes, position)))
                    };
                }

                search!(MemmemSearcher::new(bytes))
            }
            ComparisonOpExpr::Matches(regex) => lhs.compile_with(compiler, false, regex),
            ComparisonOpExpr::Wildcard(wildcard) => lhs.compile_with(compiler, false, wildcard),
            ComparisonOpExpr::StrictWildcard(wildcard) => {
                lhs.compile_with(compiler, false, wildcard)
            }
            ComparisonOpExpr::OneOf(values) => match values {
                LiteralSet::Ip(ranges) => {
                    let mut v4 = Vec::new();
                    let mut v6 = Vec::new();
                    for range in ranges.into_iter() {
                        match range.into() {
                            ExplicitIpRange::V4(range) => v4.push(range),
                            ExplicitIpRange::V6(range) => v6.push(range),
                        }
                    }
                    let v4 = RangeSet::from(v4);
                    let v6 = RangeSet::from(v6);

                    struct OneOfIp {
                        v4: RangeSet<Ipv4Addr>,
                        v6: RangeSet<Ipv6Addr>,
                    }

                    impl<U> Compare<U> for OneOfIp {
                        #[inline]
                        fn compare<'e>(
                            &self,
                            value: &LhsValue<'e>,
                            _: &'e ExecutionContext<'e, U>,
                        ) -> bool {
                            match cast_value!(value, Ip) {
                                IpAddr::V4(addr) => self.v4.contains(addr),
                                IpAddr::V6(addr) => self.v6.contains(addr),
                            }
                        }
                    }

                    lhs.compile_with(compiler, false, OneOfIp { v4, v6 })
                }
                LiteralSet::Int(values) => {
                    let values: RangeSet<_> = values.into_iter().map(Into::into).collect();

                    struct OneOfInt(RangeSet<i64>);

                    impl<U> Compare<U> for OneOfInt {
                        #[inline]
                        fn compare<'e>(
                            &self,
                            value: &LhsValue<'e>,
                            _: &'e ExecutionContext<'e, U>,
                        ) -> bool {
                            self.0.contains(cast_value!(value, Int))
                        }
                    }

                    lhs.compile_with(compiler, false, OneOfInt(values))
                }
                LiteralSet::Bytes(values) => {
                    let values: BTreeSet<Box<[u8]>> = values.into_iter().map(Into::into).collect();

                    struct Contains(BTreeSet<Box<[u8]>>);

                    impl<U> Compare<U> for Contains {
                        #[inline]
                        fn compare<'e>(
                            &self,
                            value: &LhsValue<'e>,
                            _: &'e ExecutionContext<'e, U>,
                        ) -> bool {
                            self.0.contains(cast_value!(value, Bytes).as_ref())
                        }
                    }

                    lhs.compile_with(compiler, false, Contains(values))
                }
                LiteralSet::Bool(_) => unreachable!(),
                LiteralSet::Map(_) => unreachable!(),
                LiteralSet::Array(_) => unreachable!(),
            },
            ComparisonOpExpr::ContainsOneOf(_values) => {
                unreachable!("Node should not be constructed as there is no syntax to do so")
            }
            ComparisonOpExpr::InList { name, list } => {
                struct InList {
                    name: ListName,
                    list: List,
                }

                impl<U> Compare<U> for InList {
                    #[inline]
                    fn compare<'e>(
                        &self,
                        value: &LhsValue<'e>,
                        ctx: &'e ExecutionContext<'e, U>,
                    ) -> bool {
                        ctx.get_list_matcher_unchecked(&self.list)
                            .match_value(self.name.as_str(), value)
                    }
                }

                lhs.compile_with(compiler, false, InList { name, list })
            }
        }
    }
}

#[cfg(test)]
#[allow(clippy::bool_assert_comparison)]
mod tests {
    use super::*;
    use crate::ast::ValueExpr;
    use crate::ast::function_expr::{FunctionCallArgExpr, FunctionCallExpr};
    use crate::ast::logical_expr::{LogicalExpr, QuantifierArgExpr, QuantifierOp};
    use crate::execution_context::ExecutionContext;
    use crate::functions::{
        CompiledFunction, FunctionArgKind, FunctionArgs, FunctionDefinition,
        FunctionDefinitionContext, FunctionParam, FunctionParamError, SimpleFunctionDefinition,
        SimpleFunctionImpl, SimpleFunctionOptParam, SimpleFunctionParam,
    };
    use crate::lhs_types::{Array, Map};
    use crate::list_matcher::{ListDefinition, ListMatcher};
    use crate::rhs_types::{IpRange, RegexFormat};
    use crate::scheme::{FieldIndex, IndexAccessError, Scheme};
    use crate::types::ExpectedType;
    use crate::{
        BytesFormat, FieldRef, LhsValue, ParserSettings, SchemeBuilder, SimpleFunctionArgKind,
        TypedMap,
    };
    use cidr::IpCidr;
    use serde::Deserialize;
    use std::convert::TryFrom;
    use std::iter::once;
    use std::net::IpAddr;
    use std::sync::LazyLock;
    use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};

    static COUNTING_LIMIT_CALLS: AtomicUsize = AtomicUsize::new(0);

    fn counting_limit_function<'a>(_: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        COUNTING_LIMIT_CALLS.fetch_add(1, AtomicOrdering::Relaxed);
        Some(LhsValue::Int(443))
    }

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        args.next()?.ok()
    }

    fn lowercase_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        let input = args.next()?.ok()?;
        match input {
            LhsValue::Bytes(bytes) => Some(LhsValue::Bytes(bytes.to_ascii_lowercase().into())),
            _ => panic!("Invalid type: expected Bytes, got {input:?}"),
        }
    }

    #[allow(clippy::unnecessary_wraps)]
    fn concat_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        let mut output = Vec::new();
        for (index, arg) in args.enumerate() {
            match arg.unwrap() {
                LhsValue::Bytes(bytes) => {
                    output.extend_from_slice(&bytes);
                }
                arg => panic!("Invalid type for argument {index:?}: expected Bytes, got {arg:?}"),
            }
        }
        Some(LhsValue::Bytes(output.into()))
    }

    #[derive(Debug)]
    struct FilterFunction {}

    impl FilterFunction {
        fn new() -> Self {
            Self {}
        }
    }

    impl FunctionDefinition for FilterFunction {
        fn check_param(
            &self,
            _: &ParserSettings,
            params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            next_param: &FunctionParam<'_>,
            _: Option<&mut FunctionDefinitionContext>,
        ) -> Result<(), FunctionParamError> {
            match params.len() {
                0 => {
                    next_param.arg_kind().expect(FunctionArgKind::Field)?;
                    next_param.expect_val_type(once(ExpectedType::Array))?;
                }
                1 => {
                    next_param.arg_kind().expect(FunctionArgKind::Field)?;
                    next_param.expect_val_type(once(ExpectedType::Type(Type::Array(
                        Type::Bool.into(),
                    ))))?;
                }
                _ => unreachable!(),
            }
            Ok(())
        }

        fn return_type(
            &self,
            params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<&FunctionDefinitionContext>,
        ) -> Type {
            params.next().unwrap().get_type()
        }

        /// Number of arguments needed by the function.
        fn arg_count(&self) -> (usize, Option<usize>) {
            (2, Some(0))
        }

        fn compile(
            &self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<FunctionDefinitionContext>,
        ) -> CompiledFunction {
            Box::new(|args| {
                let value_array = Array::try_from(args.next().unwrap().unwrap()).unwrap();
                let keep_array = Array::try_from(args.next().unwrap().unwrap()).unwrap();
                let output = Array::try_from_iter(
                    value_array.value_type(),
                    value_array
                        .into_iter()
                        .zip(keep_array)
                        .filter_map(|(value, keep)| {
                            if bool::try_from(keep).unwrap() {
                                Some(value)
                            } else {
                                None
                            }
                        }),
                )
                .unwrap();
                Some(LhsValue::Array(output))
            })
        }
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i64::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    #[derive(Debug, PartialEq, Eq, Serialize, Clone)]
    pub struct NumMListDefinition {}

    impl ListDefinition for NumMListDefinition {
        fn deserialize_matcher<'de>(
            &self,
            _: Type,
            deserializer: &mut dyn erased_serde::Deserializer<'de>,
        ) -> Result<Box<dyn ListMatcher>, erased_serde::Error> {
            let matcher = erased_serde::deserialize::<NumMatcher>(deserializer)?;
            Ok(Box::new(matcher))
        }

        fn new_matcher(&self) -> Box<dyn ListMatcher> {
            Box::new(NumMatcher {})
        }
    }

    static SCHEME: LazyLock<Scheme> = LazyLock::new(|| {
        let mut builder = Scheme! {
            http.cookies: Array(Bytes),
            http.headers: Map(Bytes),
            http.host: Bytes,
            ip.addr: Ip,
            ssl: Bool,
            tcp.port: Int,
            tcp.ports: Array(Int),
            array.of.bool: Array(Bool),
            map.bool.arr: Map(Array(Bool)),
            map.bytes.arr: Map(Array(Bytes)),
            http.parts: Array(Array(Bytes)),
        };
        builder.add_field("ab", Type::Ip).unwrap();
        builder.add_field("ab.cd", Type::Bytes).unwrap();
        builder.add_field("ab.cdint", Type::Int).unwrap();
        builder.add_field("r", Type::Bytes).unwrap();
        builder
            .add_optional_field("http.other_host", Type::Bytes)
            .unwrap();
        builder
            .add_field("ip.addrs", Type::Array(Type::Ip.into()))
            .unwrap();
        builder.add_optional_field("ip.limit", Type::Ip).unwrap();
        builder.add_optional_field("tcp.limit", Type::Int).unwrap();
        builder.add_optional_field("_tcp_limit", Type::Int).unwrap();
        builder
            .add_optional_field("tcp.optional", Type::Int)
            .unwrap();
        builder
            .add_function(
                "echo",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(echo_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "echo_ip",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Ip,
                    }],
                    opt_params: vec![],
                    return_type: Type::Ip,
                    implementation: SimpleFunctionImpl::new(echo_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "lowercase",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(lowercase_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "concat",
                SimpleFunctionDefinition {
                    params: vec![],
                    opt_params: vec![
                        SimpleFunctionOptParam {
                            arg_kind: SimpleFunctionArgKind::Field,
                            default_value: "".into(),
                        },
                        SimpleFunctionOptParam {
                            arg_kind: SimpleFunctionArgKind::Literal,
                            default_value: "".into(),
                        },
                    ],
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(concat_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "concat_fields",
                SimpleFunctionDefinition {
                    params: vec![
                        SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Field,
                            val_type: Type::Bytes,
                        },
                        SimpleFunctionParam {
                            arg_kind: SimpleFunctionArgKind::Field,
                            val_type: Type::Bytes,
                        },
                    ],
                    opt_params: vec![],
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(concat_function),
                },
            )
            .unwrap();
        builder
            .add_function("filter", FilterFunction::new())
            .unwrap();
        builder
            .add_function(
                "len",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: SimpleFunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(len_function),
                },
            )
            .unwrap();
        builder
            .add_function(
                "counting_limit",
                SimpleFunctionDefinition {
                    params: vec![],
                    opt_params: vec![],
                    return_type: Type::Int,
                    implementation: SimpleFunctionImpl::new(counting_limit_function),
                },
            )
            .unwrap();
        builder.add_list(Type::Int, NumMListDefinition {}).unwrap();
        builder.build()
    });

    fn field(name: &'static str) -> FieldRef<'static> {
        SCHEME.get_field(name).unwrap()
    }

    #[test]
    fn test_is_true() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("ssl"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("ssl").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::IsTrue
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "ssl",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("ssl"), true).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("ssl"), false).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_ip_compare() {
        assert!(
            FilterParser::new(&SCHEME)
                .lex_as::<ComparisonExpr>("ip.addr == 10.10.10.10")
                .is_ok()
        );

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("ip.addr <= 10:20:30:40:50:60:70:80"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("ip.addr").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThanEqual,
                    rhs: ComparisonRhs::Literal(LiteralValue::Ip(IpAddr::from([
                        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80
                    ])))
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "ip.addr",
                "op": "LessThanEqual",
                "rhs": "10:20:30:40:50:60:70:80"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(
            field("ip.addr"),
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]),
        )
        .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(
            field("ip.addr"),
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x81]),
        )
        .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([127, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_bytes_compare() {
        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<ComparisonExpr>("http.host == 10.10.10.10"),
            LexErrorKind::ExpectedName("byte separator"),
            "."
        );

        assert!(
            FilterParser::new(&SCHEME)
                .lex_as::<ComparisonExpr>(r#"http.host == "10.10.10.10""#)
                .is_ok()
        );

        // just check that parsing doesn't conflict with IPv6
        {
            let expr = assert_ok!(
                FilterParser::new(&SCHEME).lex_as("http.host >= 10:20:30:40:50:60:70:80"),
                ComparisonExpr {
                    lhs: IndexExpr {
                        identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                        indexes: vec![],
                    },
                    op: ComparisonOpExpr::Ordering {
                        op: OrderingOp::GreaterThanEqual,
                        rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                            vec![0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into()
                        )),
                    },
                }
            );

            assert_json!(
                expr,
                {
                    "lhs": "http.host",
                    "op": "GreaterThanEqual",
                    "rhs": [0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]
                }
            );
        }

        // just check that parsing doesn't conflict with regular numbers
        {
            assert_err!(
                FilterParser::new(&SCHEME).lex_as::<ComparisonExpr>(r#"http.host < 12"#),
                LexErrorKind::CountMismatch {
                    name: "character",
                    actual: 0,
                    expected: 1
                },
                ""
            );

            let expr = assert_ok!(
                FilterParser::new(&SCHEME).lex_as(r#"http.host < 12:13"#),
                ComparisonExpr {
                    lhs: IndexExpr {
                        identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                        indexes: vec![],
                    },
                    op: ComparisonOpExpr::Ordering {
                        op: OrderingOp::LessThan,
                        rhs: ComparisonRhs::Literal(LiteralValue::Bytes(vec![0x12, 0x13].into(),)),
                    },
                }
            );

            assert_json!(
                expr,
                {
                    "lhs": "http.host",
                    "op": "LessThan",
                    "rhs": [0x12, 0x13]
                }
            );
        }

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.host == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_bitwise_and() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("tcp.port & 1"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("tcp.port").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Int {
                    op: IntOp::BitwiseAnd,
                    rhs: IntRhs::Literal(1),
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "BitwiseAnd",
                "rhs": 1
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("tcp.port"), 443).unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_int_in() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"tcp.port in { 80 443 2082..2083 }"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("tcp.port").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf(LiteralSet::Int(vec![
                    80.into(),
                    443.into(),
                    (2082..=2083).into()
                ])),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "OneOf",
                "rhs": [
                    { "start": 80, "end": 80 },
                    { "start": 443, "end": 443 },
                    { "start": 2082, "end": 2083 },
                ]
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 8080).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("tcp.port"), 443).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 2081).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("tcp.port"), 2082).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 2083).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 2084).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_bytes_in() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.host in { "example.org" "example.com" }"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf(LiteralSet::Bytes(
                    ["example.org", "example.com",]
                        .iter()
                        .map(|s| (*s).to_string().into())
                        .collect()
                )),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "OneOf",
                "rhs": [
                    "example.org",
                    "example.com",
                ]
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("http.host"), "example.net")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_ip_in() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as(r#"ip.addr in { 127.0.0.0/8 ::1 10.0.0.0..10.0.255.255 }"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("ip.addr").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf(LiteralSet::Ip(vec![
                    IpRange::Cidr(IpCidr::new([127, 0, 0, 0].into(), 8).unwrap()),
                    IpRange::Cidr(IpCidr::new_host([0, 0, 0, 0, 0, 0, 0, 1].into())),
                    IpRange::Explicit(ExplicitIpRange::V4(
                        [10, 0, 0, 0].into()..=[10, 0, 255, 255].into()
                    )),
                ])),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "ip.addr",
                "op": "OneOf",
                "rhs": [
                    "127.0.0.0/8",
                    "::1",
                    { "start": "10.0.0.0", "end": "10.0.255.255" },
                ]
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([127, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([127, 0, 0, 3]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([255, 255, 255, 255]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("ip.addr"), IpAddr::from([0, 0, 0, 0, 0, 0, 0, 2]))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_contains_bytes() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.host contains "abc""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Contains("abc".to_owned().into())
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Contains",
                "rhs": "abc",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("http.host"), "abc.net.au")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_contains_str() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.host contains 6F:72:67"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Contains(vec![0x6F, 0x72, 0x67].into()),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Contains",
                "rhs": [0x6F, 0x72, 0x67],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_int_compare() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"tcp.port < 8000"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("tcp.port").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThan,
                    rhs: ComparisonRhs::Literal(LiteralValue::Int(8000))
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "LessThan",
                "rhs": 8000,
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 80).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 8080).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_dynamic_int_comparison_parsing_and_serialization() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("tcp.port < _tcp_limit"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("tcp.port").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThan,
                    rhs: ComparisonRhs::Index(ScalarExpr(IndexExpr {
                        identifier: IdentifierExpr::Field(field("_tcp_limit").to_owned()),
                        indexes: vec![],
                    })),
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "LessThan",
                "rhs": {
                    "kind": "IndexExpr",
                    "value": "_tcp_limit",
                },
            }
        );
    }

    #[test]
    fn test_dynamic_int_ordering_operators() {
        let cases = [
            ("tcp.port == tcp.limit", false),
            ("tcp.port != tcp.limit", true),
            ("tcp.port < tcp.limit", true),
            ("tcp.port <= tcp.limit", true),
            ("tcp.port > tcp.limit", false),
            ("tcp.port >= tcp.limit", false),
        ];

        for (source, expected) in cases {
            let expr = FilterParser::new(&SCHEME)
                .lex_as::<ComparisonExpr>(source)
                .unwrap()
                .0
                .compile();
            let ctx = &mut ExecutionContext::new(&SCHEME);
            ctx.set_field_value(field("tcp.port"), 5).unwrap();
            ctx.set_field_value(field("tcp.limit"), 7).unwrap();
            assert_eq!(expr.execute_one(ctx), expected, "{source}");
        }
    }

    #[test]
    fn test_dynamic_bytes_ordering_operators() {
        let cases = [
            ("http.host == http.other_host", "Equal", false),
            ("http.host != http.other_host", "NotEqual", true),
            ("http.host < http.other_host", "LessThan", true),
            ("http.host <= http.other_host", "LessThanEqual", true),
            ("http.host > http.other_host", "GreaterThan", false),
            ("http.host >= http.other_host", "GreaterThanEqual", false),
        ];

        for (source, serialized_op, expected) in cases {
            let expr = FilterParser::new(&SCHEME)
                .lex_as::<ComparisonExpr>(source)
                .unwrap()
                .0;
            assert_json!(
                expr,
                {
                    "lhs": "http.host",
                    "op": serialized_op,
                    "rhs": {
                        "kind": "IndexExpr",
                        "value": "http.other_host",
                    },
                }
            );

            let expr = expr.compile();
            let ctx = &mut ExecutionContext::new(&SCHEME);
            ctx.set_field_value(field("http.host"), "alpha").unwrap();
            ctx.set_field_value(field("http.other_host"), "beta")
                .unwrap();
            assert_eq!(expr.execute_one(ctx), expected, "{source}");
        }
    }

    #[test]
    fn test_dynamic_bytes_dotted_identifier() {
        let dynamic = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("http.host == ab.cd")
            .unwrap()
            .0;
        assert_json!(
            dynamic,
            {
                "lhs": "http.host",
                "op": "Equal",
                "rhs": {
                    "kind": "IndexExpr",
                    "value": "ab.cd",
                },
            }
        );

        let dynamic = dynamic.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("http.host"), &[0xab, 0xcd][..])
            .unwrap();
        ctx.set_field_value(field("ab.cd"), &[0x00, 0x00][..])
            .unwrap();
        assert!(!dynamic.execute_one(ctx));
    }

    #[test]
    fn test_dynamic_bytes_literal_prefix_ambiguities() {
        let hex = SCHEME.parse("http.host == ab:cd").unwrap().compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("http.host"), &[0xab, 0xcd][..])
            .unwrap();
        ctx.set_field_value(field("ab"), "192.0.2.1".parse::<IpAddr>().unwrap())
            .unwrap();
        assert_eq!(hex.execute(ctx), Ok(true));

        let raw = SCHEME
            .parse(r#"http.host == r"literal""#)
            .unwrap()
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("http.host"), "literal").unwrap();
        ctx.set_field_value(field("r"), "field value").unwrap();
        assert_eq!(raw.execute(ctx), Ok(true));

        let field_expr = SCHEME.parse("http.host == r and ssl").unwrap().compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("http.host"), "field value")
            .unwrap();
        ctx.set_field_value(field("r"), "field value").unwrap();
        ctx.set_field_value(field("ssl"), true).unwrap();
        assert_eq!(field_expr.execute(ctx), Ok(true));
    }

    #[test]
    fn test_dynamic_ip_ordering_operators() {
        let cases = [
            ("ip.addr == ip.limit", false),
            ("ip.addr != ip.limit", true),
            ("ip.addr < ip.limit", true),
            ("ip.addr <= ip.limit", true),
            ("ip.addr > ip.limit", false),
            ("ip.addr >= ip.limit", false),
        ];

        for (source, expected) in cases {
            let expr = FilterParser::new(&SCHEME)
                .lex_as::<ComparisonExpr>(source)
                .unwrap()
                .0
                .compile();
            let ctx = &mut ExecutionContext::new(&SCHEME);
            ctx.set_field_value(field("ip.addr"), "192.0.2.1".parse::<IpAddr>().unwrap())
                .unwrap();
            ctx.set_field_value(field("ip.limit"), "192.0.2.2".parse::<IpAddr>().unwrap())
                .unwrap();
            assert_eq!(expr.execute_one(ctx), expected, "{source}");
        }

        let cross_family = [
            ("ip.addr == ip.limit", false),
            ("ip.addr != ip.limit", true),
            ("ip.addr < ip.limit", false),
            ("ip.addr <= ip.limit", false),
            ("ip.addr > ip.limit", false),
            ("ip.addr >= ip.limit", false),
        ];
        for (source, expected) in cross_family {
            let expr = SCHEME.parse(source).unwrap().compile();
            let ctx = &mut ExecutionContext::new(&SCHEME);
            ctx.set_field_value(field("ip.addr"), "192.0.2.1".parse::<IpAddr>().unwrap())
                .unwrap();
            ctx.set_field_value(field("ip.limit"), "2001:db8::1".parse::<IpAddr>().unwrap())
                .unwrap();
            assert_eq!(expr.execute(ctx), Ok(expected), "{source}");
        }
    }

    #[test]
    fn test_dynamic_ip_literal_ambiguity() {
        assert!(SCHEME.parse("ip.addr == 192.0.2.1or ssl").is_ok());

        let expr = SCHEME.parse("ip.addr == ab::cd").unwrap().compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("ip.addr"), "ab::cd".parse::<IpAddr>().unwrap())
            .unwrap();
        ctx.set_field_value(field("ab"), "192.0.2.1".parse::<IpAddr>().unwrap())
            .unwrap();
        assert_eq!(expr.execute(ctx), Ok(true));
    }

    #[test]
    fn test_dynamic_int_bitwise_and() {
        let expr = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.port & tcp.limit")
            .unwrap()
            .0;
        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "BitwiseAnd",
                "rhs": {
                    "kind": "IndexExpr",
                    "value": "tcp.limit",
                },
            }
        );
        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 0b1010).unwrap();
        ctx.set_field_value(field("tcp.limit"), 0b0100).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("tcp.limit"), 0b0010).unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_dynamic_int_index_and_function_rhs() {
        let indexed = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.port == tcp.ports[0]")
            .unwrap()
            .0
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("tcp.port"), 443).unwrap();
        ctx.set_field_value(field("tcp.ports"), Array::from_iter([443, 80]))
            .unwrap();
        assert_eq!(indexed.execute_one(ctx), true);

        let function = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.port == len(http.host)")
            .unwrap()
            .0
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("tcp.port"), 11).unwrap();
        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(function.execute_one(ctx), true);
    }

    #[test]
    fn test_dynamic_bytes_and_ip_index_and_function_rhs() {
        let bytes_indexed = SCHEME
            .parse("http.host == http.cookies[0]")
            .unwrap()
            .compile();
        let bytes_function = SCHEME
            .parse("http.host == echo(http.other_host)")
            .unwrap()
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("http.host"), "value").unwrap();
        ctx.set_field_value(field("http.cookies"), Array::from_iter(["value"]))
            .unwrap();
        ctx.set_field_value(field("http.other_host"), "value")
            .unwrap();
        assert_eq!(bytes_indexed.execute(ctx), Ok(true));
        assert_eq!(bytes_function.execute(ctx), Ok(true));

        let ip_indexed = SCHEME.parse("ip.addr == ip.addrs[0]").unwrap().compile();
        let ip_function = SCHEME
            .parse("ip.addr == echo_ip(ip.limit)")
            .unwrap()
            .compile();
        let addr = "192.0.2.1".parse::<IpAddr>().unwrap();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("ip.addr"), addr).unwrap();
        ctx.set_field_value(field("ip.addrs"), Array::from_iter([addr]))
            .unwrap();
        ctx.set_field_value(field("ip.limit"), addr).unwrap();
        assert_eq!(ip_indexed.execute(ctx), Ok(true));
        assert_eq!(ip_function.execute(ctx), Ok(true));
    }

    #[test]
    fn test_dynamic_rhs_type_validation() {
        let (kind, _) = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.port == http.host")
            .unwrap_err();
        assert_eq!(
            kind,
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Int.into(),
                actual: Type::Bytes,
            })
        );

        let (kind, _) = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.port == tcp.ports[*]")
            .unwrap_err();
        assert_eq!(
            kind,
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Int.into(),
                actual: Type::Array(Type::Int.into()),
            })
        );

        let (kind, _) = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("http.host == tcp.limit")
            .unwrap_err();
        assert_eq!(
            kind,
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: Type::Int,
            })
        );

        // A dotted identifier is type-checked as a whole, not as a byte literal.
        let (kind, _) = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("http.host == ab.cdint")
            .unwrap_err();
        assert_eq!(
            kind,
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: Type::Int,
            })
        );

        let (kind, _) = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("ip.addr == http.host")
            .unwrap_err();
        assert_eq!(
            kind,
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Ip.into(),
                actual: Type::Bytes,
            })
        );

        let (kind, _) = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("http.host == http.cookies[*]")
            .unwrap_err();
        assert_eq!(
            kind,
            LexErrorKind::TypeMismatch(TypeMismatchError {
                expected: Type::Bytes.into(),
                actual: Type::Array(Type::Bytes.into()),
            })
        );
    }

    #[test]
    fn test_scalar_expr_validation_and_conversion() {
        let index = IndexExpr {
            identifier: IdentifierExpr::Field(field("tcp.limit").to_owned()),
            indexes: vec![],
        };
        let scalar = ScalarExpr::try_from(index.clone()).unwrap();
        assert_eq!(scalar.as_index_expr(), &index);
        assert_eq!(scalar.get_type(), Type::Int);

        let int_scalar = ScalarIntExpr::try_from(scalar.clone()).unwrap();
        assert_eq!(int_scalar.as_index_expr(), &index);
        assert_eq!(ScalarExpr::from(int_scalar.clone()), scalar);
        assert_eq!(IndexExpr::from(int_scalar.clone()), index);
        assert_eq!(IntRhs::Index(int_scalar).get_type(), Type::Int);
        assert_eq!(IntRhs::Literal(42).get_type(), Type::Int);
        assert_eq!(IndexExpr::from(scalar), index);

        let bytes = IndexExpr {
            identifier: IdentifierExpr::Field(field("http.host").to_owned()),
            indexes: vec![],
        };
        let scalar_bytes = ScalarExpr::try_from(bytes.clone()).unwrap();
        assert_eq!(scalar_bytes.get_type(), Type::Bytes);
        assert_eq!(
            ScalarIntExpr::try_from(scalar_bytes),
            Err(TypeMismatchError {
                expected: Type::Int.into(),
                actual: Type::Bytes,
            })
        );

        let mut expected = ExpectedTypeList::default();
        expected.insert(Type::Bytes);
        expected.insert(Type::Int);
        expected.insert(Type::Ip);

        let ip = IndexExpr {
            identifier: IdentifierExpr::Field(field("ip.addr").to_owned()),
            indexes: vec![],
        };
        let scalar_ip = ScalarExpr::try_from(ip.clone()).unwrap();
        assert_eq!(scalar_ip.get_type(), Type::Ip);
        assert_eq!(
            ScalarIntExpr::try_from(scalar_ip.clone()),
            Err(TypeMismatchError {
                expected: Type::Int.into(),
                actual: Type::Ip,
            })
        );
        assert_eq!(IndexExpr::from(scalar_ip), ip);

        let bool_expr = IndexExpr {
            identifier: IdentifierExpr::Field(field("ssl").to_owned()),
            indexes: vec![],
        };
        assert_eq!(
            ScalarExpr::try_from(bool_expr),
            Err(TypeMismatchError {
                expected: expected.clone(),
                actual: Type::Bool,
            })
        );

        let mapped = IndexExpr {
            identifier: IdentifierExpr::Field(field("tcp.ports").to_owned()),
            indexes: vec![FieldIndex::MapEach],
        };
        assert_eq!(
            ScalarExpr::try_from(mapped),
            Err(TypeMismatchError {
                expected,
                actual: Type::Array(Type::Int.into()),
            })
        );
    }

    #[test]
    fn test_scalar_expr_mutable_visitor_preserves_invariants() {
        struct AddMapEach;

        impl<'a> VisitorMut<'a> for AddMapEach {
            fn visit_index_expr(&mut self, expr: &'a mut IndexExpr) {
                expr.indexes.push(FieldIndex::MapEach);
            }
        }

        let index = IndexExpr {
            identifier: IdentifierExpr::Field(field("tcp.limit").to_owned()),
            indexes: vec![],
        };
        let mut scalar = ScalarExpr::try_from(index.clone()).unwrap();
        AddMapEach.visit_scalar_expr(&mut scalar);
        assert_eq!(scalar.as_index_expr(), &index);

        let mut scalar_int = ScalarIntExpr::try_from(index.clone()).unwrap();
        AddMapEach.visit_scalar_int_expr(&mut scalar_int);
        assert_eq!(scalar_int.as_index_expr(), &index);
    }

    #[test]
    fn test_dynamic_int_missing_values() {
        let expr = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.optional != tcp.limit")
            .unwrap()
            .0
            .compile();

        let rhs_only = &mut ExecutionContext::new(&SCHEME);
        rhs_only.set_field_value(field("tcp.limit"), 7).unwrap();
        assert_eq!(expr.execute_one(rhs_only), true);

        let lhs_only = &mut ExecutionContext::new(&SCHEME);
        lhs_only.set_field_value(field("tcp.optional"), 5).unwrap();
        assert_eq!(expr.execute_one(lhs_only), false);

        let neither = &mut ExecutionContext::new(&SCHEME);
        assert_eq!(expr.execute_one(neither), false);
    }

    #[test]
    fn test_dynamic_not_equal_missing_lhs_with_nil_behavior_false() {
        let mut builder = SchemeBuilder::new();
        builder.add_optional_field("lhs", Type::Int).unwrap();
        builder.add_optional_field("rhs", Type::Int).unwrap();
        builder.set_nil_not_equal_behavior(false);
        let scheme = builder.build();
        let expr = scheme.parse("lhs != rhs").unwrap().compile();
        let ctx = &mut ExecutionContext::new(&scheme);
        ctx.set_field_value(scheme.get_field("rhs").unwrap(), 1)
            .unwrap();
        assert_eq!(expr.execute(ctx), Ok(false));
    }

    #[test]
    fn test_dynamic_int_mapped_lhs_broadcast() {
        let expr = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.ports[*] >= tcp.limit")
            .unwrap()
            .0
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("tcp.ports"), Array::from_iter([80, 443, 8080]))
            .unwrap();
        ctx.set_field_value(field("tcp.limit"), 443).unwrap();
        assert_eq!(expr.execute_vec(ctx), [false, true, true]);

        let missing_rhs = &mut ExecutionContext::new(&SCHEME);
        missing_rhs
            .set_field_value(field("tcp.ports"), Array::from_iter([80, 443, 8080]))
            .unwrap();
        assert_eq!(expr.execute_vec(missing_rhs), [false, false, false]);
    }

    #[test]
    fn test_dynamic_bytes_and_ip_mapped_lhs_broadcast() {
        let bytes = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("http.cookies[*] >= http.other_host")
            .unwrap()
            .0
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("http.cookies"), Array::from_iter(["alpha", "beta"]))
            .unwrap();
        ctx.set_field_value(field("http.other_host"), "beta")
            .unwrap();
        assert_eq!(bytes.execute_vec(ctx), [false, true]);

        let missing_rhs = &mut ExecutionContext::new(&SCHEME);
        missing_rhs
            .set_field_value(field("http.cookies"), Array::from_iter(["alpha", "beta"]))
            .unwrap();
        assert_eq!(bytes.execute_vec(missing_rhs), [false, false]);

        let ips = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("ip.addrs[*] < ip.limit")
            .unwrap()
            .0
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(
            field("ip.addrs"),
            Array::from_iter([
                "192.0.2.1".parse::<IpAddr>().unwrap(),
                "192.0.2.3".parse::<IpAddr>().unwrap(),
            ]),
        )
        .unwrap();
        ctx.set_field_value(field("ip.limit"), "192.0.2.2".parse::<IpAddr>().unwrap())
            .unwrap();
        assert_eq!(ips.execute_vec(ctx), [true, false]);
    }

    #[test]
    fn test_dynamic_int_mapped_lhs_evaluates_rhs_once() {
        COUNTING_LIMIT_CALLS.store(0, AtomicOrdering::Relaxed);
        let expr = FilterParser::new(&SCHEME)
            .lex_as::<ComparisonExpr>("tcp.ports[*] >= counting_limit()")
            .unwrap()
            .0
            .compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(field("tcp.ports"), Array::from_iter([80, 443, 8080]))
            .unwrap();

        assert_eq!(expr.execute_vec(ctx), [false, true, true]);
        assert_eq!(COUNTING_LIMIT_CALLS.load(AtomicOrdering::Relaxed), 1);

        assert_eq!(expr.execute_vec(ctx), [false, true, true]);
        assert_eq!(COUNTING_LIMIT_CALLS.load(AtomicOrdering::Relaxed), 2);
    }

    #[test]
    fn test_dynamic_int_rhs_is_visited() {
        let ast = SCHEME.parse("tcp.port == tcp.limit").unwrap();
        assert_eq!(ast.uses("tcp.port"), Ok(true));
        assert_eq!(ast.uses("tcp.limit"), Ok(true));
        assert_eq!(ast.uses("http.host"), Ok(false));

        let ast = SCHEME.parse("tcp.port & tcp.limit").unwrap();
        assert_eq!(ast.uses("tcp.limit"), Ok(true));
    }

    #[test]
    fn test_array_contains_str() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.cookies[0] contains "abc""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Contains("abc".to_owned().into()),
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = Array::from_iter(["abc"]);

        ctx.set_field_value(field("http.cookies"), cookies).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        let cookies = Array::from_iter(["def"]);

        ctx.set_field_value(field("http.cookies"), cookies).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_map_of_bytes_contains_str() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.headers["host"] contains "abc""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.headers").to_owned()),
                    indexes: vec![FieldIndex::MapKey("host".to_string())],
                },
                op: ComparisonOpExpr::Contains("abc".to_owned().into()),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.headers",
                    {"kind": "MapKey", "value": "host"}
                ],
                "op": "Contains",
                "rhs": "abc",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::from({
            let mut map = TypedMap::new();
            map.insert(b"host".to_vec().into(), "example.org");
            map
        });

        ctx.set_field_value(field("http.headers"), headers).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        let headers = LhsValue::from({
            let mut map = TypedMap::new();
            map.insert(b"host".to_vec().into(), "abc.net.au");
            map
        });

        ctx.set_field_value(field("http.headers"), headers).unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_echo_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"echo(http.host) == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("echo").unwrap().to_owned(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                            indexes: vec![],
                        })],
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_eq!(expr.lhs.identifier.get_type(), Type::Bytes);
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "echo",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.com")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_lowercase_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"lowercase(http.host) == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("lowercase").unwrap().to_owned(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                            indexes: vec![],
                        })],
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_eq!(expr.lhs.identifier.get_type(), Type::Bytes);
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "lowercase",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "EXAMPLE.COM")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("http.host"), "EXAMPLE.ORG")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_missing_array_value_equal() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.cookies[0] == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.cookies",
                    {"kind": "ArrayIndex", "value": 0}
                ],
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.cookies"), Array::new(Type::Bytes))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_missing_array_value_not_equal() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.cookies[0] != "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::NotEqual,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.cookies",
                    {"kind": "ArrayIndex", "value": 0}
                ],
                "op": "NotEqual",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.cookies"), Array::new(Type::Bytes))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_missing_map_value_equal() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.headers["missing"] == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.headers").to_owned()),
                    indexes: vec![FieldIndex::MapKey("missing".into())],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.headers",
                    {"kind": "MapKey", "value": "missing"}
                ],
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.headers"), Map::new(Type::Bytes))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_missing_map_value_not_equal() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.headers["missing"] != "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.headers").to_owned()),
                    indexes: vec![FieldIndex::MapKey("missing".into())],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::NotEqual,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": [
                    "http.headers",
                    {"kind": "MapKey", "value": "missing"}
                ],
                "op": "NotEqual",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.headers"), Map::new(Type::Bytes))
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_concat_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"concat(http.host) == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap().to_owned(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                            indexes: vec![],
                        })],
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_eq!(expr.lhs.identifier.get_type(), Type::Bytes);
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "concat",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example.org")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("http.host"), "example.co.uk")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"concat(http.host, ".org") == "example.org""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap().to_owned(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::from(
                                ".org".to_owned()
                            ))),
                        ],
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(
                        "example.org".to_owned().into()
                    ))
                }
            }
        );

        assert_eq!(expr.lhs.identifier.get_type(), Type::Bytes);
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "concat",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        },
                        {
                            "kind": "Literal",
                            "value": ".org"
                        },
                    ]
                },
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "example").unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("http.host"), "cloudflare")
            .unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_filter_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as(r#"filter(http.cookies, array.of.bool)[0] == "three""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("filter").unwrap().to_owned(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(
                                    field("array.of.bool").to_owned()
                                ),
                                indexes: vec![],
                            }),
                        ],
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("three".to_owned().into()))
                }
            }
        );

        assert_eq!(
            expr.lhs.identifier.get_type(),
            Type::Array(Type::Bytes.into())
        );
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "filter",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": "http.cookies"
                            },
                            {
                                "kind": "IndexExpr",
                                "value": "array.of.bool"
                            }
                        ]
                    },
                    {"kind": "ArrayIndex", "value": 0},
                ],
                "op": "Equal",
                "rhs": "three"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = Array::from_iter(["one", "two", "three"]);
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        let booleans = Array::from_iter([false, false, true]);
        ctx.set_field_value(field("array.of.bool"), booleans)
            .unwrap();

        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_map_each_on_array_with_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"concat(http.cookies[*], "-cf")[2] == "three-cf""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap().to_owned(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(2)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("three-cf".to_owned().into()))
                }
            }
        );

        assert_eq!(
            expr.lhs.identifier.get_type(),
            Type::Array(Type::Bytes.into())
        );
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "concat",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.cookies", {"kind": "MapEach"}],
                            },
                            {
                                "kind": "Literal",
                                "value": "-cf"
                            }
                        ]
                    },
                    {"kind": "ArrayIndex", "value": 2},
                ],
                "op": "Equal",
                "rhs": "three-cf"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = Array::from_iter(["one", "two", "three"]);
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_map_each_on_map_with_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as(r#"concat(http.headers[*], "-cf")[2] in {"one-cf" "two-cf" "three-cf"}"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap().to_owned(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(field("http.headers").to_owned()),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(2)],
                },
                op: ComparisonOpExpr::OneOf(LiteralSet::Bytes(vec![
                    "one-cf".to_owned().into(),
                    "two-cf".to_owned().into(),
                    "three-cf".to_owned().into()
                ]))
            }
        );

        assert_eq!(
            expr.lhs.identifier.get_type(),
            Type::Array(Type::Bytes.into())
        );
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "concat",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.headers", {"kind": "MapEach"}],
                            },
                            {
                                "kind": "Literal",
                                "value": "-cf"
                            }
                        ]
                    },
                    {"kind": "ArrayIndex", "value": 2},
                ],
                "op": "OneOf",
                "rhs": ["one-cf", "two-cf", "three-cf"],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::from({
            let mut map = TypedMap::new();
            map.insert(b"0".to_vec().into(), "one");
            map.insert(b"1".to_vec().into(), "two");
            map.insert(b"2".to_vec().into(), "three");
            map
        });
        ctx.set_field_value(field("http.headers"), headers).unwrap();

        assert_eq!(expr.execute_one(ctx), true);
    }

    // The non-mapped argument (the "-cf" literal) must be applied to *every*
    // mapped element, even though it is now evaluated only once per call.
    #[test]
    fn test_map_each_function_non_mapped_arg_applied_to_all_elements() {
        let (expr, rest) = FilterParser::new(&SCHEME)
            .lex_as::<FunctionCallExpr>(r#"concat(http.cookies[*], "-cf")"#)
            .unwrap();
        assert_eq!(rest, "");

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(
            field("http.cookies"),
            Array::from_iter(["one", "two", "three"]),
        )
        .unwrap();

        assert_eq!(
            expr.execute(ctx),
            Ok(LhsValue::Array(Array::from_iter([
                "one-cf", "two-cf", "three-cf"
            ])))
        );
    }

    // A non-mapped argument that is expensive to re-evaluate (here a nested
    // function call) is evaluated once and reused for every mapped element.
    #[test]
    fn test_map_each_memoizes_expensive_non_mapped_arg() {
        let (expr, rest) = FilterParser::new(&SCHEME)
            .lex_as::<FunctionCallExpr>(r#"concat_fields(http.cookies[*], lowercase(http.host))"#)
            .unwrap();
        assert_eq!(rest, "");

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(
            field("http.cookies"),
            Array::from_iter(["one", "two", "three"]),
        )
        .unwrap();
        ctx.set_field_value(field("http.host"), "SUFFIX").unwrap();

        // `lowercase(http.host)` == "suffix" is appended to every element.
        assert_eq!(
            expr.execute(ctx),
            Ok(LhsValue::Array(Array::from_iter([
                "onesuffix",
                "twosuffix",
                "threesuffix"
            ])))
        );
    }

    // map_each over a Map with no extra args: exercises the fused Map -> Array
    // path (no intermediate array allocation) and the empty-args fast path.
    #[test]
    fn test_map_each_on_map_no_extra_args() {
        let (expr, rest) = FilterParser::new(&SCHEME)
            .lex_as::<FunctionCallExpr>(r#"lowercase(http.headers[*])"#)
            .unwrap();
        assert_eq!(rest, "");

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);
        let headers = LhsValue::from({
            let mut map = TypedMap::new();
            map.insert(b"0".to_vec().into(), "ONE");
            map.insert(b"1".to_vec().into(), "TWO");
            map.insert(b"2".to_vec().into(), "THREE");
            map
        });
        ctx.set_field_value(field("http.headers"), headers).unwrap();

        assert_eq!(
            expr.execute(ctx),
            Ok(LhsValue::Array(Array::from_iter(["one", "two", "three"])))
        );
    }

    #[test]
    fn test_map_each_on_array_for_cmp() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.cookies[*] == "three""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("three".to_owned().into()))
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": ["http.cookies", {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "three",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = Array::from_iter(["one", "two", "three"]);
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(expr.execute_vec(ctx), [false, false, true]);
    }

    #[test]
    fn test_map_each_on_map_for_cmp() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.headers[*] == "three""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.headers").to_owned()),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("three".to_owned().into()))
                }
            }
        );

        assert_eq!(
            expr.lhs.identifier.get_type(),
            Type::Map(Type::Bytes.into())
        );
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": ["http.headers", {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "three",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::from({
            let mut map = TypedMap::new();
            map.insert(b"0".to_vec().into(), "one");
            map.insert(b"1".to_vec().into(), "two");
            map.insert(b"2".to_vec().into(), "three");
            map
        });
        ctx.set_field_value(field("http.headers"), headers).unwrap();

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr.execute_vec(ctx).iter() {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 2);
        assert_eq!(true_count, 1);
    }

    #[test]
    fn test_map_each_on_array_full() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"concat(http.cookies[*], "-cf")[*] == "three-cf""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap().to_owned(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        context: None,
                    }),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("three-cf".to_owned().into()))
                }
            }
        );

        assert_eq!(
            expr.lhs.identifier.get_type(),
            Type::Array(Type::Bytes.into())
        );
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "concat",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.cookies", {"kind": "MapEach"}],
                            },
                            {
                                "kind": "Literal",
                                "value": "-cf"
                            }
                        ]
                    },
                    {"kind": "MapEach"},
                ],
                "op": "Equal",
                "rhs": "three-cf"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = Array::from_iter(["one", "two", "three"]);
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(expr.execute_vec(ctx), [false, false, true]);
    }

    #[test]
    fn test_map_each_on_array_len_function() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"len(http.cookies[*])[*] > 3"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("len").unwrap().to_owned(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            identifier: IdentifierExpr::Field(field("http.cookies").to_owned()),
                            indexes: vec![FieldIndex::MapEach],
                        }),],
                        context: None,
                    }),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::GreaterThan,
                    rhs: ComparisonRhs::Literal(LiteralValue::Int(3)),
                }
            }
        );

        assert_eq!(
            expr.lhs.identifier.get_type(),
            Type::Array(Type::Int.into())
        );
        assert_eq!(expr.lhs.get_type(), Type::Int);
        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": [
                    {
                        "name": "len",
                        "args": [
                            {
                                "kind": "IndexExpr",
                                "value": ["http.cookies", {"kind": "MapEach"}],
                            }
                        ]
                    },
                    {"kind": "MapEach"},
                ],
                "op": "GreaterThan",
                "rhs": 3
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = Array::from_iter(["one", "two", "three"]);
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(expr.execute_vec(ctx), [false, false, true]);
    }

    #[test]
    fn test_map_each_error() {
        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<ComparisonExpr>(r#"http.host[*] == "three""#),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<ComparisonExpr>(r#"ip.addr[*] == 127.0.0.1"#),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Ip,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<ComparisonExpr>(r#"ssl[*]"#),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bool,
            }),
            "[*]"
        );

        assert_err!(
            FilterParser::new(&SCHEME).lex_as::<ComparisonExpr>(r#"tcp.port[*] == 80"#),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Int,
            }),
            "[*]"
        );
    }

    #[derive(Debug, PartialEq, Eq, Serialize, Clone, Deserialize)]
    pub struct NumMatcher {}

    impl ListMatcher for NumMatcher {
        fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool {
            // Ideally this would lookup list_name in metadata
            let list_id = if list_name == "even" {
                [0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
            } else {
                [1u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
            };

            match val {
                LhsValue::Int(num) => self.num_matches(*num, list_id),
                _ => unreachable!(), // TODO: is this unreachable?
            }
        }

        fn clear(&mut self) {}
    }

    /// Match IPs (v4 and v6) in lists.
    ///
    /// ```text
    /// ip.src in $whitelist and not origin.ip in $whitelist
    /// ```
    impl NumMatcher {
        fn num_matches(&self, num: i64, list_id: [u8; 16]) -> bool {
            let remainder =
                i64::from(list_id == [1u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
            num % 2 == remainder
        }
    }

    #[test]
    fn test_number_in_list() {
        let list = SCHEME.get_list(&Type::Int).unwrap();
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"tcp.port in $even"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("tcp.port").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::InList {
                    list: list.to_owned(),
                    name: ListName::from("even".to_string())
                }
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "tcp.port",
                "op": "InList",
                "rhs": "even"
            }
        );

        // EVEN list
        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 1000).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 1001).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        // ODD list
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"tcp.port in $odd"#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("tcp.port").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::InList {
                    list: list.to_owned(),
                    name: ListName::from("odd".to_string()),
                }
            }
        );
        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("tcp.port"), 1000).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("tcp.port"), 1001).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        let json = serde_json::to_string(ctx).unwrap();
        assert_eq!(
            json,
            "{\"tcp.port\":1001,\"$lists\":[{\"type\":\"Int\",\"data\":{}}]}"
        );
    }

    #[test]
    fn test_any_number_in_list() {
        let list = SCHEME.get_list(&Type::Int).unwrap();
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"any(tcp.ports[*] in $even)"#),
            LogicalExpr::Quantifier {
                op: QuantifierOp::Any,
                arg: Box::new(QuantifierArgExpr::Logical(LogicalExpr::Comparison(
                    ComparisonExpr {
                        lhs: IndexExpr {
                            identifier: IdentifierExpr::Field(field("tcp.ports").to_owned()),
                            indexes: vec![FieldIndex::MapEach],
                        },
                        op: ComparisonOpExpr::InList {
                            list: list.to_owned(),
                            name: ListName::from("even".to_string()),
                        },
                    }
                ))),
            }
        );

        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "op": "Any",
                "arg": {
                    "kind": "SimpleExpr",
                    "value": {
                        "lhs": ["tcp.ports", {"kind": "MapEach"}],
                        "op": "InList",
                        "rhs": "even"
                    }
                }
            }
        );

        // EVEN list
        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        // 1 odd, 1 even
        let arr1 = Array::from_iter([1001, 1000]);

        ctx.set_field_value(field("tcp.ports"), arr1).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        // All odd numbers
        let arr2 = Array::from_iter([1001, 1003]);

        ctx.set_field_value(field("tcp.ports"), arr2).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_any_all_functions_with_missing_arrays() {
        let ctx = &mut ExecutionContext::new(&SCHEME);
        ctx.set_field_value(
            field("map.bool.arr"),
            Map::new(Type::Array(Type::Bool.into())),
        )
        .unwrap();
        ctx.set_field_value(
            field("map.bytes.arr"),
            Map::new(Type::Array(Type::Bytes.into())),
        )
        .unwrap();

        let execute = |input| SCHEME.parse(input).unwrap().compile().execute(ctx).unwrap();

        assert_eq!(execute(r#"any(map.bool.arr["missing"])"#), false);
        assert_eq!(execute(r#"all(map.bool.arr["missing"])"#), false);
        assert_eq!(
            execute(r#"any(map.bytes.arr["missing"][*] matches "bar")"#),
            false
        );
        assert_eq!(
            execute(r#"all(map.bytes.arr["missing"][*] matches "bar")"#),
            true
        );
    }

    #[test]
    fn test_map_each_nested() {
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.parts[*][*] == "[5][5]""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.parts").to_owned()),
                    indexes: vec![FieldIndex::MapEach, FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("[5][5]".to_owned().into()))
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": ["http.parts", {"kind": "MapEach"}, {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "[5][5]",
            }
        );

        let expr1 = expr.compile();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.parts[5][*] == "[5][5]""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.parts").to_owned()),
                    indexes: vec![FieldIndex::ArrayIndex(5), FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("[5][5]".to_owned().into()))
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": ["http.parts", {"kind": "ArrayIndex", "value": 5}, {"kind": "MapEach"}],
                "op": "Equal",
                "rhs": "[5][5]",
            }
        );

        let expr2 = expr.compile();

        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#"http.parts[*][5] == "[5][5]""#),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.parts").to_owned()),
                    indexes: vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(5)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes("[5][5]".to_owned().into()))
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Type::Bool.into()));

        assert_json!(
            expr,
            {
                "lhs": ["http.parts", {"kind": "MapEach"}, {"kind": "ArrayIndex", "value": 5}],
                "op": "Equal",
                "rhs": "[5][5]",
            }
        );

        let expr3 = expr.compile();

        let ctx = &mut ExecutionContext::new(&SCHEME);

        let parts = Array::try_from_iter(
            Type::Array(Type::Bytes.into()),
            (0..10).map(|i| Array::from_iter((0..10).map(|j| format!("[{i}][{j}]")))),
        )
        .unwrap();

        ctx.set_field_value(field("http.parts"), parts).unwrap();

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr1.execute_vec(ctx).iter() {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 99);
        assert_eq!(true_count, 1);

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr2.execute_vec(ctx).iter() {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 9);
        assert_eq!(true_count, 1);

        let mut true_count = 0;
        let mut false_count = 0;
        for val in expr3.execute_vec(ctx).iter() {
            if *val {
                true_count += 1;
            } else {
                false_count += 1;
            }
        }
        assert_eq!(false_count, 9);
        assert_eq!(true_count, 1);
    }

    #[test]
    fn test_raw_string() {
        // Equal operator
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("http.host == r###\"ab\"###"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(BytesExpr::new(
                        "ab".as_bytes(),
                        BytesFormat::Raw(3),
                    ))),
                },
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Equal",
                "rhs": "ab",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "ab").unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("http.host"), "cd").unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        // Matches operator
        let parser = FilterParser::new(&SCHEME);
        let r = Regex::new("a.b", RegexFormat::Literal, parser.settings()).unwrap();
        let expr = assert_ok!(
            parser.lex_as("http.host matches r###\"a.b\"###"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Matches(r),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Matches",
                "rhs": "a.b",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "axb").unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("http.host"), "axc").unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        // Wildcard operator
        let wildcard = Wildcard::new(
            BytesExpr::new(r"foo*\*\\".as_bytes(), BytesFormat::Raw(2)),
            usize::MAX,
        )
        .unwrap();
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as(r#####"http.host wildcard r##"foo*\*\\"##"#####),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Wildcard(wildcard),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Wildcard",
                "rhs": r"foo*\*\\",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), r"foo*\").unwrap();
        assert!(expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foo*").unwrap();
        assert!(!expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foo\").unwrap();
        assert!(!expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"Foo*\").unwrap();
        assert!(expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foobarmumble*\")
            .unwrap();
        assert!(expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foobarmumble\")
            .unwrap();
        assert!(!expr.execute_one(ctx));

        // Strict wildcard operator
        let wildcard = Wildcard::new(
            BytesExpr::new(r"foo*\*\\".as_bytes(), BytesFormat::Raw(2)),
            usize::MAX,
        )
        .unwrap();
        let expr = assert_ok!(
            FilterParser::new(&SCHEME)
                .lex_as(r#####"http.host strict wildcard r##"foo*\*\\"##"#####),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::StrictWildcard(wildcard),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": "http.host",
                "op": "Strict Wildcard",
                "rhs": r"foo*\*\\",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), r"foo*\").unwrap();
        assert!(expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foo*").unwrap();
        assert!(!expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foo\").unwrap();
        assert!(!expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"Foo*\").unwrap();
        assert!(!expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foobarmumble*\")
            .unwrap();
        assert!(expr.execute_one(ctx));
        ctx.set_field_value(field("http.host"), r"foobarmumble\")
            .unwrap();
        assert!(!expr.execute_one(ctx));

        // Function call
        let expr = assert_ok!(
            FilterParser::new(&SCHEME).lex_as("concat(http.host, r#\"cd\"#) == r##\"abcd\"##"),
            ComparisonExpr {
                lhs: IndexExpr {
                    identifier: IdentifierExpr::FunctionCallExpr(FunctionCallExpr {
                        function: SCHEME.get_function("concat").unwrap().to_owned(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                identifier: IdentifierExpr::Field(field("http.host").to_owned()),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::Literal(LiteralValue::Bytes(BytesExpr::new(
                                "cd".as_bytes(),
                                BytesFormat::Raw(1)
                            )))
                        ],
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: ComparisonRhs::Literal(LiteralValue::Bytes(BytesExpr::new(
                        "abcd".as_bytes(),
                        BytesFormat::Raw(2)
                    )))
                }
            }
        );

        assert_eq!(expr.lhs.identifier.get_type(), Type::Bytes);
        assert_eq!(expr.lhs.get_type(), Type::Bytes);
        assert_eq!(expr.get_type(), Type::Bool);

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "concat",
                    "args": [
                        {
                            "kind": "IndexExpr",
                            "value": "http.host"
                        },
                        {
                            "kind": "Literal",
                            "value": "cd"
                        }
                    ]
                },
                "op": "Equal",
                "rhs": "abcd"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value(field("http.host"), "xx").unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("http.host"), "ab").unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn expression_evaluation_wildcard() {
        let op_normal = |rhs, value, expected| -> Vec<(&str, &str, &[u8], bool)> {
            vec![("wildcard", rhs, value, expected)]
        };
        let op_strict = |rhs, value, expected| -> Vec<(&str, &str, &[u8], bool)> {
            vec![("strict wildcard", rhs, value, expected)]
        };
        let op_both = |rhs, value, expected| -> Vec<(&str, &str, &[u8], bool)> {
            op_normal(rhs, value, expected)
                .into_iter()
                .chain(op_strict(rhs, value, expected))
                .collect()
        };

        let testcases = [
            // Escaping at the wildcard-level with raw strings.
            op_both(r##"r"foo?*\*\\""##, r"foo?*\".as_bytes(), true),
            op_both(r##"r#"foo?*\*\\"#"##, r"foo?*\".as_bytes(), true),
            op_both(r##"r"foo?*\*\\""##, r"foo?bar*\".as_bytes(), true),
            op_both(r##"r"foo?*\*\\""##, r"foo?x\".as_bytes(), false),
            op_both(r##"r"¯\\_(ツ*)_/¯""##, r"¯\_(ツ)_/¯".as_bytes(), true),
            // Escaping at the wildcard-level with quoted strings.
            op_both(r#""foo?*\\*\\\\""#, r"foo?*\".as_bytes(), true),
            op_both(r#""foo?*\\*\\\\""#, r"foo?*\".as_bytes(), true),
            op_both(r#""foo?*\\*\\\\""#, r"foo?bar*\".as_bytes(), true),
            op_both(r#""foo?*\\*\\\\""#, r"foo?x\".as_bytes(), false),
            op_both(r#""fo\x6f""#, r"foo".as_bytes(), true),
            op_both(r#""¯\\\\_(ツ*)_/¯""#, r"¯\_(ツ)_/¯".as_bytes(), true),
            op_both(r#""\xaa\x22""#, &[0xaa, 0x22], true),
            // ? is not special.
            op_both(r##""?""##, r"?".as_bytes(), true),
            op_both(r##""?""##, r"x".as_bytes(), false),
            // Case sensitivity.
            op_normal(r##""a""##, r"A".as_bytes(), true),
            op_strict(r##""a""##, r"A".as_bytes(), false),
        ]
        .concat();

        for t @ (op, rhs, value, expected) in testcases {
            let expr: ComparisonExpr = FilterParser::new(&SCHEME)
                .lex_as(&format!("http.host {op} {rhs}"))
                .map(|(e, _)| e)
                .expect("failed to parse expression");
            let expr = expr.compile();
            let ctx = &mut ExecutionContext::new(&SCHEME);

            ctx.set_field_value(field("http.host"), value).unwrap();

            assert_eq!(expr.execute_one(ctx), expected, "failed test case {t:?}");
        }
    }

    #[test]
    fn test_optional_fields() {
        let mut builder = SchemeBuilder::new();
        builder
            .add_optional_field("tcp.srcport", Type::Int)
            .unwrap();
        builder
            .add_optional_field("tcp.dstport", Type::Int)
            .unwrap();
        builder
            .add_optional_field("tcp.flags.syn", Type::Bool)
            .unwrap();
        builder
            .add_optional_field("udp.srcport", Type::Int)
            .unwrap();
        builder
            .add_optional_field("udp.dstport", Type::Int)
            .unwrap();
        builder.set_nil_not_equal_behavior(false);
        let scheme = builder.build();

        macro_rules! test_case {
            ($filter:ident {$($name:ident $(. $suffix:ident)*: $value:literal),*} => $outcome:literal) => {{
                #[allow(unused_mut)]
                let mut ctx = ExecutionContext::<()>::new(&scheme);
                $(
                    ctx.set_field_value(scheme.get_field(stringify!($name $(. $suffix)*)).unwrap(), $value).unwrap();
                )*

                assert_eq!($filter.execute(&ctx), Ok($outcome));
            }};
        }

        let filter = scheme
            .parse("(tcp.dstport != 80) or (udp.dstport != 80)")
            .unwrap()
            .compile();

        test_case!(filter { tcp.dstport: 443 } => true);

        test_case!(filter { tcp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 53 } => true);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter {} => false);

        let filter = scheme
            .parse("(tcp.dstport != 80) and (udp.dstport != 80)")
            .unwrap()
            .compile();

        test_case!(filter { tcp.dstport: 443 } => false);

        test_case!(filter { tcp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 53 } => false);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter {} => false);

        let filter = scheme
            .parse("(tcp.srcport == 1337) or ((tcp.dstport != 80) or (udp.dstport != 80))")
            .unwrap()
            .compile();

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 80 } => true);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 443 } => true);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 80 } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 443 } => true);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 444 } => true);

        test_case!(filter {} => false);

        let filter = scheme
            .parse("(tcp.srcport == 1337) and ((tcp.dstport != 80) or (udp.dstport != 80))")
            .unwrap()
            .compile();

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 80 } => false);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 443 } => true);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 80 } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 443 } => false);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 444 } => false);

        test_case!(filter {} => false);

        let filter = scheme
            .parse("(tcp.srcport == 1337) or ((tcp.dstport != 80) and (udp.dstport != 80))")
            .unwrap()
            .compile();

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 80 } => true);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 443 } => true);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 80 } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 443 } => false);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 444 } => false);

        test_case!(filter {} => false);

        let filter = scheme
            .parse("(tcp.srcport == 1337) and ((tcp.dstport != 80) and (udp.dstport != 80))")
            .unwrap()
            .compile();

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 80 } => false);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 443 } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 80 } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 443 } => false);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 444 } => false);

        test_case!(filter {} => false);

        let filter = scheme
            .parse("(tcp.srcport == 1337) and ((tcp.dstport != 80) and ((tcp.flags.syn) or (udp.dstport != 80)))")
            .unwrap()
            .compile();

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 80, tcp.flags.syn: true } => false);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 443, tcp.flags.syn: true } => true);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 80, tcp.flags.syn: true } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 443, tcp.flags.syn: true } => false);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 80, tcp.flags.syn: false } => false);

        test_case!(filter { tcp.srcport: 1337, tcp.dstport: 443, tcp.flags.syn: false } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 80, tcp.flags.syn: false } => false);

        test_case!(filter { tcp.srcport: 1234, tcp.dstport: 443, tcp.flags.syn: false } => false);

        test_case!(filter { udp.dstport: 80 } => false);

        test_case!(filter { udp.dstport: 444 } => false);

        test_case!(filter {} => false);

        let filter = scheme.parse("tcp.flags.syn").unwrap().compile();

        test_case!(filter { tcp.flags.syn: true } => true);

        test_case!(filter { tcp.flags.syn: false } => false);

        test_case!(filter {} => false);

        let filter = scheme.parse("not tcp.flags.syn").unwrap().compile();

        test_case!(filter { tcp.flags.syn: true } => false);

        test_case!(filter { tcp.flags.syn: false } => true);

        test_case!(filter {} => true);

        let filter = scheme.parse("not (not tcp.flags.syn)").unwrap().compile();

        test_case!(filter { tcp.flags.syn: true } => true);

        test_case!(filter { tcp.flags.syn: false } => false);

        test_case!(filter {} => false);

        let filter = scheme.parse("not (tcp.dstport eq 80)").unwrap().compile();

        test_case!(filter { tcp.dstport: 80 } => false);

        test_case!(filter { tcp.dstport: 443 } => true);

        test_case!(filter {} => true);

        let filter = scheme.parse("not (tcp.dstport ne 80)").unwrap().compile();

        test_case!(filter { tcp.dstport: 80 } => true);

        test_case!(filter { tcp.dstport: 443 } => false);

        test_case!(filter {} => true);
    }
}
