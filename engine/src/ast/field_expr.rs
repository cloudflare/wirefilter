// use crate::filter::CompiledExpr;
use super::{function_expr::FunctionCallExpr, visitor::Visitor, Expr};
use crate::{
    ast::index_expr::IndexExpr,
    compiler::{Compiler, ExecCtx},
    filter::{CompiledExpr, CompiledValueExpr},
    heap_searcher::HeapSearcher,
    lex::{expect, skip_space, span, Lex, LexErrorKind, LexResult, LexWith},
    list_matcher::ListMatcher,
    range_set::RangeSet,
    rhs_types::{Bytes, ExplicitIpRange, List, Regex},
    scheme::{Field, Identifier, Scheme},
    strict_partial_ord::StrictPartialOrd,
    types::{GetType, LhsValue, RhsValue, RhsValues, Type},
};
use fnv::FnvBuildHasher;
use indexmap::IndexSet;
use memmem::Searcher;
use serde::{Serialize, Serializer};
use std::{cmp::Ordering, net::IpAddr};

const LESS: u8 = 0b001;
const GREATER: u8 = 0b010;
const EQUAL: u8 = 0b100;

lex_enum!(#[repr(u8)] OrderingOp {
    "eq" | "==" => Equal = EQUAL,
    "ne" | "!=" => NotEqual = LESS | GREATER,
    "ge" | ">=" => GreaterThanEqual = GREATER | EQUAL,
    "le" | "<=" => LessThanEqual = LESS | EQUAL,
    "gt" | ">" => GreaterThan = GREATER,
    "lt" | "<" => LessThan = LESS,
});

impl OrderingOp {
    pub fn matches(self, ordering: Ordering) -> bool {
        let mask = self as u8;
        let flag = match ordering {
            Ordering::Less => LESS,
            Ordering::Greater => GREATER,
            Ordering::Equal => EQUAL,
        };
        mask & flag != 0
    }

    pub fn matches_opt(self, ordering: Option<Ordering>) -> bool {
        match ordering {
            Some(ordering) => self.matches(ordering),
            // only `!=` should be true for incomparable types
            None => self == OrderingOp::NotEqual,
        }
    }
}

lex_enum!(IntOp {
    "&" | "bitwise_and" => BitwiseAnd,
});

lex_enum!(BytesOp {
    "contains" => Contains,
    "~" | "matches" => Matches,
});

lex_enum!(ComparisonOp {
    "in" => In,
    OrderingOp => Ordering,
    IntOp => Int,
    BytesOp => Bytes,
});

/// Operator and right-hand side expression of a
/// comparison expression.
#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
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
        /// Right-hand side literal
        rhs: RhsValue,
    },

    /// Integer comparison
    Int {
        /// Integer comparison operator:
        /// * "&" | "bitwise_and"
        op: IntOp,
        /// Right-hand side integer value
        rhs: i32,
    },

    /// "contains" comparison
    #[serde(serialize_with = "serialize_contains")]
    Contains(Bytes),

    /// "matches / ~" comparison
    #[serde(serialize_with = "serialize_matches")]
    Matches(Regex),

    /// "in {...}" comparison
    #[serde(serialize_with = "serialize_one_of")]
    OneOf(RhsValues),

    /// "in $..." comparison
    #[serde(serialize_with = "serialize_list")]
    InList(List),
}

fn serialize_op_rhs<T: Serialize, S: Serializer>(
    op: &'static str,
    rhs: &T,
    ser: S,
) -> Result<S::Ok, S::Error> {
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

fn serialize_contains<S: Serializer>(rhs: &Bytes, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Contains", rhs, ser)
}

fn serialize_matches<S: Serializer>(rhs: &Regex, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Matches", rhs, ser)
}

fn serialize_one_of<S: Serializer>(rhs: &RhsValues, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("OneOf", rhs, ser)
}

fn serialize_list<S: Serializer>(rhs: &List, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("InList", rhs, ser)
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub(crate) enum LhsFieldExpr<'s> {
    Field(Field<'s>),
    FunctionCallExpr(FunctionCallExpr<'s>),
}

impl<'s> LhsFieldExpr<'s> {
    pub fn compile_with_compiler<C: Compiler + 's>(
        self,
        compiler: &mut C,
    ) -> CompiledValueExpr<'s, C> {
        match self {
            LhsFieldExpr::Field(f) => CompiledValueExpr::new(move |ctx: &C::ExecutionContext| {
                Ok(ctx.get_field_value_unchecked(f).as_ref())
            }),
            LhsFieldExpr::FunctionCallExpr(call) => compiler.compile_function_call_expr(call),
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for LhsFieldExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (item, input) = Identifier::lex_with(input, scheme)?;
        match item {
            Identifier::Field(field) => Ok((LhsFieldExpr::Field(field), input)),
            Identifier::Function(function) => FunctionCallExpr::lex_with_function(input, function)
                .map(|(call, input)| (LhsFieldExpr::FunctionCallExpr(call), input)),
        }
    }
}

impl<'s> GetType for LhsFieldExpr<'s> {
    fn get_type(&self) -> Type {
        match self {
            LhsFieldExpr::Field(field) => field.get_type(),
            LhsFieldExpr::FunctionCallExpr(call) => call.get_type(),
        }
    }
}

/// Comparison expression
#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
pub struct ComparisonExpr<'s> {
    /// Lef-hand side of the comparison expression
    pub lhs: IndexExpr<'s>,

    /// Operator + right-hand side of the comparison expression
    #[serde(flatten)]
    pub op: ComparisonOpExpr,
}

impl<'s> GetType for ComparisonExpr<'s> {
    fn get_type(&self) -> Type {
        if self.lhs.map_each_count() > 0 {
            Type::Array(Box::new(Type::Bool))
        } else if self.op == ComparisonOpExpr::IsTrue {
            // Bool or Array(Bool)
            self.lhs.get_type()
        } else {
            Type::Bool
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for ComparisonExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let (lhs, input) = IndexExpr::lex_with(input, scheme)?;

        Self::lex_with_lhs(input, scheme, lhs)
    }
}

impl<'s> ComparisonExpr<'s> {
    pub(crate) fn lex_with_lhs<'i>(
        input: &'i str,
        _scheme: &'s Scheme,
        lhs: IndexExpr<'s>,
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
                        lhs_type: Type::Array(Box::new(Type::Array(Box::new(Type::Bool)))),
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
                        let (list, input) = List::lex(input)?;
                        (ComparisonOpExpr::InList(list), input)
                    } else {
                        let (rhs, input) = RhsValues::lex_with(input, lhs_type)?;
                        (ComparisonOpExpr::OneOf(rhs), input)
                    }
                }
                (Type::Ip, ComparisonOp::Ordering(op))
                | (Type::Bytes, ComparisonOp::Ordering(op))
                | (Type::Int, ComparisonOp::Ordering(op)) => {
                    let (rhs, input) = RhsValue::lex_with(input, lhs_type)?;
                    (ComparisonOpExpr::Ordering { op, rhs }, input)
                }
                (Type::Int, ComparisonOp::Int(op)) => {
                    let (rhs, input) = i32::lex(input)?;
                    (ComparisonOpExpr::Int { op, rhs }, input)
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                    BytesOp::Contains => {
                        let (bytes, input) = Bytes::lex(input)?;
                        (ComparisonOpExpr::Contains(bytes), input)
                    }
                    BytesOp::Matches => {
                        let (regex, input) = Regex::lex(input)?;
                        (ComparisonOpExpr::Matches(regex), input)
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
}

impl<'s> Expr<'s> for ComparisonExpr<'s> {
    fn walk<T, V: Visitor<'s, T>>(&self, visitor: &mut V) -> Option<T> {
        visitor.visit_index_expr(&self.lhs)
    }

    fn compile_with_compiler<C: Compiler + 's>(self, compiler: &mut C) -> CompiledExpr<'s, C> {
        let lhs = self.lhs;

        macro_rules! cast_value {
            ($value:expr, $ty:ident) => {
                match $value {
                    LhsValue::$ty(value) => value,
                    _ => unreachable!(),
                }
            };
        }

        match self.op {
            ComparisonOpExpr::IsTrue => {
                if lhs.get_type() == Type::Bool {
                    lhs.compile_with(compiler, false, move |x, _ctx| *cast_value!(x, Bool))
                } else if lhs.get_type().next() == Some(Type::Bool) {
                    // MapEach is impossible in this case, thus call `compile_vec_with` directly
                    // to coerce LhsValue to Vec<bool>
                    CompiledExpr::Vec(
                        lhs.compile_vec_with(compiler, move |x, _ctx| *cast_value!(x, Bool)),
                    )
                } else {
                    unreachable!()
                }
            }
            ComparisonOpExpr::Ordering { op, rhs } => match op {
                OrderingOp::NotEqual => lhs.compile_with(compiler, true, move |x, _ctx| {
                    op.matches_opt(x.strict_partial_cmp(&rhs))
                }),
                _ => lhs.compile_with(compiler, false, move |x, _ctx| {
                    op.matches_opt(x.strict_partial_cmp(&rhs))
                }),
            },
            ComparisonOpExpr::Int {
                op: IntOp::BitwiseAnd,
                rhs,
            } => lhs.compile_with(compiler, false, move |x, _ctx| {
                cast_value!(x, Int) & rhs != 0
            }),
            ComparisonOpExpr::Contains(bytes) => {
                let searcher = HeapSearcher::from(bytes);

                lhs.compile_with(compiler, false, move |x, _ctx| {
                    searcher.search_in(cast_value!(x, Bytes)).is_some()
                })
            }
            ComparisonOpExpr::Matches(regex) => {
                lhs.compile_with(compiler, false, move |x, _ctx| {
                    regex.is_match(cast_value!(x, Bytes))
                })
            }
            ComparisonOpExpr::OneOf(values) => match values {
                RhsValues::Ip(ranges) => {
                    let mut v4 = Vec::new();
                    let mut v6 = Vec::new();
                    for range in ranges {
                        match range.clone().into() {
                            ExplicitIpRange::V4(range) => v4.push(range),
                            ExplicitIpRange::V6(range) => v6.push(range),
                        }
                    }
                    let v4 = RangeSet::from(v4);
                    let v6 = RangeSet::from(v6);

                    lhs.compile_with(compiler, false, move |x, _ctx| match cast_value!(x, Ip) {
                        IpAddr::V4(addr) => v4.contains(addr),
                        IpAddr::V6(addr) => v6.contains(addr),
                    })
                }
                RhsValues::Int(values) => {
                    let values: RangeSet<_> = values.iter().cloned().collect();

                    lhs.compile_with(compiler, false, move |x, _ctx| {
                        values.contains(cast_value!(x, Int))
                    })
                }
                RhsValues::Bytes(values) => {
                    let values: IndexSet<Box<[u8]>, FnvBuildHasher> =
                        values.into_iter().map(Into::into).collect();

                    lhs.compile_with(compiler, false, move |x, _ctx| {
                        values.contains(cast_value!(x, Bytes) as &[u8])
                    })
                }
                RhsValues::Bool(_) => unreachable!(),
                RhsValues::Map(_) => unreachable!(),
                RhsValues::Array(_) => unreachable!(),
            },
            ComparisonOpExpr::InList(list) => lhs.compile_with(compiler, false, move |val, ctx| {
                ctx.get_list_matcher_unchecked(&val.get_type())
                    .match_value(list.name(), &val)
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::function_expr::{FunctionCallArgExpr, FunctionCallExpr},
        ast::simple_expr::SimpleExpr,
        execution_context::ExecutionContext,
        functions::{
            FunctionArgKind, FunctionArgs, FunctionDefinition, FunctionDefinitionContext,
            FunctionParam, FunctionParamError, SimpleFunctionDefinition, SimpleFunctionImpl,
            SimpleFunctionOptParam, SimpleFunctionParam,
        },
        lhs_types::{Array, Map},
        list_matcher::ListMatcherWrapper,
        rhs_types::IpRange,
        scheme::{FieldIndex, IndexAccessError},
        types::ExpectedType,
    };
    use cidr::{Cidr, IpCidr};
    use lazy_static::lazy_static;
    use std::{convert::TryFrom, iter::once, net::IpAddr};

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

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        Some(args.next()?.ok()?)
    }

    fn lowercase_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        let input = args.next()?.ok()?;
        match input {
            LhsValue::Bytes(bytes) => Some(LhsValue::Bytes(bytes.to_ascii_lowercase().into())),
            _ => panic!("Invalid type: expected Bytes, got {:?}", input),
        }
    }

    fn concat_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        let mut output = Vec::new();
        for (index, arg) in args.enumerate() {
            match arg.unwrap() {
                LhsValue::Bytes(bytes) => {
                    output.extend_from_slice(&bytes);
                }
                arg => panic!(
                    "Invalid type for argument {:?}: expected Bytes, got {:?}",
                    index, arg
                ),
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
            params: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            next_param: &FunctionParam<'_>,
            _: Option<&mut FunctionDefinitionContext>,
        ) -> Result<(), FunctionParamError> {
            match params.len() {
                0 => {
                    next_param.expect_arg_kind(FunctionArgKind::Field)?;
                    next_param.expect_val_type(once(ExpectedType::Array))?;
                }
                1 => {
                    next_param.expect_arg_kind(FunctionArgKind::Field)?;
                    next_param.expect_val_type(once(ExpectedType::Type(Type::Array(Box::new(
                        Type::Bool,
                    )))))?;
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

        fn compile<'s>(
            &'s self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<FunctionDefinitionContext>,
        ) -> Box<dyn for<'a> Fn(FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 's>
        {
            Box::new(|args| {
                let value_array = Array::try_from(args.next().unwrap().unwrap()).unwrap();
                let keep_array = Array::try_from(args.next().unwrap().unwrap()).unwrap();
                let mut output = Array::new(value_array.value_type().clone());
                let mut i = 0;
                for (value, keep) in value_array.into_iter().zip(keep_array) {
                    if bool::try_from(keep).unwrap() {
                        output.insert(i, value).unwrap();
                        i += 1;
                    }
                }
                Some(LhsValue::Array(output))
            })
        }
    }

    fn len_function<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
        match args.next()? {
            Ok(LhsValue::Bytes(bytes)) => Some(LhsValue::Int(i32::try_from(bytes.len()).unwrap())),
            Err(Type::Bytes) => None,
            _ => unreachable!(),
        }
    }

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme: Scheme = Scheme! {
                http.cookies: Array(Bytes),
                http.headers: Map(Bytes),
                http.host: Bytes,
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
                tcp.ports: Array(Int),
                array.of.bool: Array(Bool),
                http.parts: Array(Array(Bytes)),
            };
            scheme
                .add_function(
                    "any".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Array(Box::new(Type::Bool)),
                        }],
                        opt_params: vec![],
                        return_type: Type::Bool,
                        implementation: SimpleFunctionImpl::new(any_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "echo".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(echo_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "lowercase".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(lowercase_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "concat".into(),
                    SimpleFunctionDefinition {
                        params: vec![],
                        opt_params: vec![
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Field,
                                default_value: "".into(),
                            },
                            SimpleFunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: "".into(),
                            },
                        ],
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(concat_function),
                    },
                )
                .unwrap();
            scheme
                .add_function("filter".into(), FilterFunction::new())
                .unwrap();
            scheme
                .add_function(
                    "len".into(),
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
        };
    }

    fn field(name: &'static str) -> Field<'static> {
        SCHEME.get_field(name).unwrap()
    }

    #[test]
    fn test_is_true() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with("ssl", &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ssl")),
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
        let expr = assert_ok!(
            ComparisonExpr::lex_with("ip.addr <= 10:20:30:40:50:60:70:80", &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ip.addr")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThanEqual,
                    rhs: RhsValue::Ip(IpAddr::from([
                        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80
                    ]))
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
        // just check that parsing doesn't conflict with IPv6
        {
            let expr = assert_ok!(
                ComparisonExpr::lex_with("http.host >= 10:20:30:40:50:60:70:80", &SCHEME),
                ComparisonExpr {
                    lhs: IndexExpr {
                        lhs: LhsFieldExpr::Field(field("http.host")),
                        indexes: vec![],
                    },
                    op: ComparisonOpExpr::Ordering {
                        op: OrderingOp::GreaterThanEqual,
                        rhs: RhsValue::Bytes(
                            vec![0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into()
                        ),
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
            let expr = assert_ok!(
                ComparisonExpr::lex_with(r#"http.host < 12"#, &SCHEME),
                ComparisonExpr {
                    lhs: IndexExpr {
                        lhs: LhsFieldExpr::Field(field("http.host")),
                        indexes: vec![],
                    },
                    op: ComparisonOpExpr::Ordering {
                        op: OrderingOp::LessThan,
                        rhs: RhsValue::Bytes(vec![0x12].into()),
                    },
                }
            );

            assert_json!(
                expr,
                {
                    "lhs": "http.host",
                    "op": "LessThan",
                    "rhs": [0x12]
                }
            );
        }

        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"http.host == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
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
            ComparisonExpr::lex_with("tcp.port & 1", &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Int {
                    op: IntOp::BitwiseAnd,
                    rhs: 1,
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
            ComparisonExpr::lex_with(r#"tcp.port in { 80 443 2082..2083 }"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf(RhsValues::Int(vec![80..=80, 443..=443, 2082..=2083])),
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
            ComparisonExpr::lex_with(r#"http.host in { "example.org" "example.com" }"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf(RhsValues::Bytes(
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
            ComparisonExpr::lex_with(
                r#"ip.addr in { 127.0.0.0/8 ::1 10.0.0.0..10.0.255.255 }"#,
                &SCHEME
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ip.addr")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::OneOf(RhsValues::Ip(vec![
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
            ComparisonExpr::lex_with(r#"http.host contains "abc""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
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
            ComparisonExpr::lex_with(r#"http.host contains 6F:72:67"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
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
            ComparisonExpr::lex_with(r#"tcp.port < 8000"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::LessThan,
                    rhs: RhsValue::Int(8000)
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
    fn test_array_contains_str() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"http.cookies[0] contains "abc""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Contains("abc".to_owned().into()),
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "abc".into()).unwrap();
            arr
        });

        ctx.set_field_value(field("http.cookies"), cookies).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "def".into()).unwrap();
            arr
        });

        ctx.set_field_value(field("http.cookies"), cookies).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_map_of_bytes_contains_str() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"http.headers["host"] contains "abc""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
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

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"host", "example.org".into()).unwrap();
            map
        });

        ctx.set_field_value(field("http.headers"), headers).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"host", "abc.net.au".into()).unwrap();
            map
        });

        ctx.set_field_value(field("http.headers"), headers).unwrap();
        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_echo_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"echo(http.host) == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("echo"),
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

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
            ComparisonExpr::lex_with(r#"lowercase(http.host) == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("lowercase"),
                        function: SCHEME.get_function("lowercase").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

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
            ComparisonExpr::lex_with(r#"http.cookies[0] == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
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
            ComparisonExpr::lex_with(r#"http.cookies[0] != "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::NotEqual,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
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
            ComparisonExpr::lex_with(r#"http.headers["missing"] == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapKey("missing".into())],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
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
            ComparisonExpr::lex_with(r#"http.headers["missing"] != "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapKey("missing".into())],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::NotEqual,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
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
            ComparisonExpr::lex_with(r#"concat(http.host) == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("concat"),
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

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
            ComparisonExpr::lex_with(r#"concat(http.host, ".org") == "example.org""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("concat"),
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.host")),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                ".org".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

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
            ComparisonExpr::lex_with(
                r#"filter(http.cookies, array.of.bool)[0] == "three""#,
                &SCHEME
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("filter"),
                        function: SCHEME.get_function("filter").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.cookies")),
                                indexes: vec![],
                            }),
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("array.of.bool")),
                                indexes: vec![],
                            }),
                        ],
                        return_type: Type::Array(Box::new(Type::Bytes)),
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("three".to_owned().into())
                }
            }
        );

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

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        let booleans = LhsValue::Array({
            let mut arr = Array::new(Type::Bool);
            arr.insert(0, false.into()).unwrap();
            arr.insert(1, false.into()).unwrap();
            arr.insert(2, true.into()).unwrap();
            arr
        });
        ctx.set_field_value(field("array.of.bool"), booleans)
            .unwrap();

        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_map_each_on_array_with_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(
                r#"concat(http.cookies[*], "-cf")[2] == "three-cf""#,
                &SCHEME
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("concat"),
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.cookies")),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(2)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("three-cf".to_owned().into())
                }
            }
        );

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

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_map_each_on_map_with_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(
                r#"concat(http.headers[*], "-cf")[2] in {"one-cf" "two-cf" "three-cf"}"#,
                &SCHEME
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("concat"),
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.headers")),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::ArrayIndex(2)],
                },
                op: ComparisonOpExpr::OneOf(RhsValues::Bytes(vec![
                    "one-cf".to_owned().into(),
                    "two-cf".to_owned().into(),
                    "three-cf".to_owned().into()
                ]))
            }
        );

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

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"0", "one".into()).unwrap();
            map.insert(b"1", "two".into()).unwrap();
            map.insert(b"2", "three".into()).unwrap();
            map
        });
        ctx.set_field_value(field("http.headers"), headers).unwrap();

        assert_eq!(expr.execute_one(ctx), true);
    }

    #[test]
    fn test_map_each_on_array_for_cmp() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"http.cookies[*] == "three""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("three".to_owned().into())
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

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![false, false, true].into_boxed_slice()
        );
    }

    #[test]
    fn test_map_each_on_map_for_cmp() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"http.headers[*] == "three""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("three".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

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

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert(b"0", "one".into()).unwrap();
            map.insert(b"1", "two".into()).unwrap();
            map.insert(b"2", "three".into()).unwrap();
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
            ComparisonExpr::lex_with(
                r#"concat(http.cookies[*], "-cf")[*] == "three-cf""#,
                &SCHEME
            ),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("concat"),
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![
                            FunctionCallArgExpr::IndexExpr(IndexExpr {
                                lhs: LhsFieldExpr::Field(field("http.cookies")),
                                indexes: vec![FieldIndex::MapEach],
                            }),
                            FunctionCallArgExpr::Literal(RhsValue::Bytes(Bytes::from(
                                "-cf".to_owned()
                            ))),
                        ],
                        return_type: Type::Bytes,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("three-cf".to_owned().into())
                }
            }
        );

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

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![false, false, true].into_boxed_slice()
        );
    }

    #[test]
    fn test_map_each_on_array_len_function() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"len(http.cookies[*])[*] > 3"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("len"),
                        function: SCHEME.get_function("len").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.cookies")),
                            indexes: vec![FieldIndex::MapEach],
                        }),],
                        return_type: Type::Int,
                        context: None,
                    }),
                    indexes: vec![FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::GreaterThan,
                    rhs: RhsValue::Int(3),
                }
            }
        );

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

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "one".into()).unwrap();
            arr.insert(1, "two".into()).unwrap();
            arr.insert(2, "three".into()).unwrap();
            arr
        });
        ctx.set_field_value(field("http.cookies"), cookies).unwrap();

        assert_eq!(
            expr.execute_vec(ctx),
            vec![false, false, true].into_boxed_slice()
        );
    }

    #[test]
    fn test_map_each_error() {
        assert_err!(
            ComparisonExpr::lex_with(r#"http.host[*] == "three""#, &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bytes,
            }),
            "[*]"
        );

        assert_err!(
            ComparisonExpr::lex_with(r#"ip.addr[*] == 127.0.0.1"#, &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Ip,
            }),
            "[*]"
        );

        assert_err!(
            ComparisonExpr::lex_with(r#"ssl[*]"#, &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Bool,
            }),
            "[*]"
        );

        assert_err!(
            ComparisonExpr::lex_with(r#"tcp.port[*] == 80"#, &SCHEME),
            LexErrorKind::InvalidIndexAccess(IndexAccessError {
                index: FieldIndex::MapEach,
                actual: Type::Int,
            }),
            "[*]"
        );
    }

    #[derive(Debug, PartialEq, Serialize, Clone)]
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

        fn to_json_value(&self) -> serde_json::Value {
            serde_json::from_str(&serde_json::ser::to_string(self).unwrap()).unwrap()
        }
    }

    /// Match IPs (v4 and v6) in lists.
    ///
    /// ```text
    /// ip.src in $whitelist and not origin.ip in $whitelist
    /// ```
    impl NumMatcher {
        pub fn new() -> Self {
            NumMatcher {}
        }

        fn num_matches(&self, num: i32, list_id: [u8; 16]) -> bool {
            let remainder = if list_id == [1u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] {
                1
            } else {
                0
            };

            num % 2 == remainder
        }
    }

    #[test]
    fn test_number_in_list() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"tcp.port in $even"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::InList(List::from("even".to_string()))
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

        let list_matcher = NumMatcher::new();
        ctx.set_list_matcher(Type::Int, ListMatcherWrapper::new(list_matcher));

        ctx.set_field_value(field("tcp.port"), 1000).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        ctx.set_field_value(field("tcp.port"), 1001).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        // ODD list
        let expr = ComparisonExpr::lex_with(r#"tcp.port in $odd"#, &SCHEME)
            .unwrap()
            .0;
        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let list_matcher = NumMatcher::new();
        ctx.set_list_matcher(Type::Int, ListMatcherWrapper::new(list_matcher));

        ctx.set_field_value(field("tcp.port"), 1000).unwrap();
        assert_eq!(expr.execute_one(ctx), false);

        ctx.set_field_value(field("tcp.port"), 1001).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        let json = serde_json::to_string(ctx).unwrap();
        assert_eq!(json, "{\"tcp.port\":1001,\"Int\":{}}");
    }

    #[test]
    fn test_any_number_in_list() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"any(tcp.ports[*] in $even)"#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("any"),
                        function: SCHEME.get_function("any").unwrap(),
                        args: vec![FunctionCallArgExpr::SimpleExpr(SimpleExpr::Comparison(
                            ComparisonExpr {
                                lhs: IndexExpr {
                                    lhs: LhsFieldExpr::Field(field("tcp.ports")),
                                    indexes: vec![FieldIndex::MapEach],
                                },
                                op: ComparisonOpExpr::InList(List::from("even".to_string())),
                            }
                        ))],
                        return_type: Type::Bool,
                        context: None,
                    }),
                    indexes: vec![],
                },
                op: ComparisonOpExpr::IsTrue
            }
        );

        assert_json!(
            expr,
            {
                "lhs": {
                    "name": "any",
                    "args": [
                        {
                            "kind": "SimpleExpr",
                            "value": {
                                "lhs": ["tcp.ports", {"kind": "MapEach"}],
                                "op": "InList",
                                "rhs": "even"
                            }
                        }
                    ]
                },
                "op": "IsTrue"
            }
        );

        // EVEN list
        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let list_matcher = NumMatcher::new();
        ctx.set_list_matcher(Type::Int, ListMatcherWrapper::new(list_matcher));

        let mut arr1 = Array::new(Type::Int);
        // 1 odd, 1 even
        arr1.push(1001.into()).unwrap();
        arr1.push(1000.into()).unwrap();

        ctx.set_field_value(field("tcp.ports"), arr1).unwrap();
        assert_eq!(expr.execute_one(ctx), true);

        let mut arr2 = Array::new(Type::Int);
        // all odd numbers
        arr2.push(1001.into()).unwrap();
        arr2.push(1003.into()).unwrap();

        ctx.set_field_value(field("tcp.ports"), arr2).unwrap();
        assert_eq!(expr.execute_one(ctx), false);
    }

    #[test]
    fn test_map_each_nested() {
        let expr = assert_ok!(
            ComparisonExpr::lex_with(r#"http.parts[*][*] == "[5][5]""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.parts")),
                    indexes: vec![FieldIndex::MapEach, FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("[5][5]".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

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
            ComparisonExpr::lex_with(r#"http.parts[5][*] == "[5][5]""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.parts")),
                    indexes: vec![FieldIndex::ArrayIndex(5), FieldIndex::MapEach],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("[5][5]".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

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
            ComparisonExpr::lex_with(r#"http.parts[*][5] == "[5][5]""#, &SCHEME),
            ComparisonExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.parts")),
                    indexes: vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(5)],
                },
                op: ComparisonOpExpr::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("[5][5]".to_owned().into())
                }
            }
        );

        assert_eq!(expr.get_type(), Type::Array(Box::new(Type::Bool)));

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

        let mut parts = Array::new(Type::Array(Box::new(Type::Bytes)));
        for i in 0..10 {
            let mut nested_arr = Array::new(Type::Bytes);
            for j in 0..10 {
                nested_arr
                    .push(LhsValue::Bytes(
                        format!("[{}][{}]", i, j).into_bytes().into(),
                    ))
                    .unwrap();
            }
            parts.push(LhsValue::Array(nested_arr)).unwrap();
        }

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
}
