// use crate::filter::CompiledExpr;
use super::{function_expr::FunctionCallExpr, Expr};
use crate::{
    ast::index_expr::IndexExpr,
    execution_context::ExecutionContext,
    filter::CompiledExpr,
    heap_searcher::HeapSearcher,
    lex::{skip_space, span, Lex, LexErrorKind, LexResult, LexWith},
    range_set::RangeSet,
    rhs_types::{Bytes, ExplicitIpRange, Regex},
    scheme::{Field, Scheme},
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

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
enum FieldOp {
    #[serde(serialize_with = "serialize_is_true")]
    IsTrue,

    Ordering {
        op: OrderingOp,
        rhs: RhsValue,
    },

    Int {
        op: IntOp,
        rhs: i32,
    },

    #[serde(serialize_with = "serialize_contains")]
    Contains(Bytes),

    #[serde(serialize_with = "serialize_matches")]
    Matches(Regex),

    #[serde(serialize_with = "serialize_one_of")]
    OneOf(RhsValues),
}

fn serialize_op_rhs<T: Serialize, S: Serializer>(
    op: &'static str,
    rhs: &T,
    ser: S,
) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("FieldOp", 2)?;
    out.serialize_field("op", op)?;
    out.serialize_field("rhs", rhs)?;
    out.end()
}

fn serialize_is_true<S: Serializer>(ser: S) -> Result<S::Ok, S::Error> {
    use serde::ser::SerializeStruct;

    let mut out = ser.serialize_struct("FieldOp", 1)?;
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

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub(crate) enum LhsFieldExpr<'s> {
    Field(Field<'s>),
    FunctionCallExpr(FunctionCallExpr<'s>),
}

impl<'s> LhsFieldExpr<'s> {
    pub fn uses(&self, field: Field<'s>) -> bool {
        match self {
            LhsFieldExpr::Field(f) => *f == field,
            LhsFieldExpr::FunctionCallExpr(call) => call.uses(field),
        }
    }

    pub fn execute(&'s self, ctx: &'s ExecutionContext<'s>) -> LhsValue<'s> {
        match self {
            LhsFieldExpr::Field(f) => ctx.get_field_value_unchecked(*f),
            LhsFieldExpr::FunctionCallExpr(call) => call.execute(ctx),
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for LhsFieldExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        Ok(match FunctionCallExpr::lex_with(input, scheme) {
            Ok((call, input)) => (LhsFieldExpr::FunctionCallExpr(call), input),
            Err(err @ (LexErrorKind::InvalidArgumentType { .. }, _))
            | Err(err @ (LexErrorKind::InvalidArgumentKind { .. }, _))
            | Err(err @ (LexErrorKind::InvalidArgumentsCount { .. }, _)) => Err(err)?,
            // Fallback to field
            Err(_) => {
                let (field, input) = Field::lex_with(input, scheme)?;
                (LhsFieldExpr::Field(field), input)
            }
        })
    }
}

impl<'s> GetType for LhsFieldExpr<'s> {
    fn get_type(&self) -> Type {
        match self {
            LhsFieldExpr::Field(field) => field.get_type(),
            LhsFieldExpr::FunctionCallExpr(call) => call.function.get_type(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
pub struct FieldExpr<'s> {
    lhs: IndexExpr<'s>,

    #[serde(flatten)]
    op: FieldOp,
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FieldExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        let (lhs, input) = IndexExpr::lex_with(input, scheme)?;

        let lhs_type = lhs.get_type();

        let (op, input) = if lhs_type == Type::Bool {
            (FieldOp::IsTrue, input)
        } else {
            let (op, input) = ComparisonOp::lex(skip_space(input))?;

            let input_after_op = input;

            let input = skip_space(input);

            match (&lhs_type, op) {
                (_, ComparisonOp::In) => {
                    let (rhs, input) = RhsValues::lex_with(input, lhs_type)?;
                    (FieldOp::OneOf(rhs), input)
                }
                (_, ComparisonOp::Ordering(op)) => {
                    let (rhs, input) = RhsValue::lex_with(input, lhs_type)?;
                    (FieldOp::Ordering { op, rhs }, input)
                }
                (Type::Int, ComparisonOp::Int(op)) => {
                    let (rhs, input) = i32::lex(input)?;
                    (FieldOp::Int { op, rhs }, input)
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                    BytesOp::Contains => {
                        let (bytes, input) = Bytes::lex(input)?;
                        (FieldOp::Contains(bytes), input)
                    }
                    BytesOp::Matches => {
                        let (regex, input) = Regex::lex(input)?;
                        (FieldOp::Matches(regex), input)
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

        Ok((FieldExpr { lhs, op }, input))
    }
}

impl<'s> Expr<'s> for FieldExpr<'s> {
    fn uses(&self, field: Field<'s>) -> bool {
        self.lhs.uses(field)
    }

    fn compile(self) -> CompiledExpr<'s> {
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
            FieldOp::IsTrue => lhs.compile_with(move |x| cast_value!(x, Bool)),
            FieldOp::Ordering { op, rhs } => {
                lhs.compile_with(move |x| op.matches_opt(x.strict_partial_cmp(&rhs)))
            }
            FieldOp::Int {
                op: IntOp::BitwiseAnd,
                rhs,
            } => lhs.compile_with(move |x| cast_value!(x, Int) & rhs != 0),
            FieldOp::Contains(bytes) => {
                let searcher = HeapSearcher::new(bytes);

                lhs.compile_with(move |x| searcher.search_in(&cast_value!(x, Bytes)).is_some())
            }
            FieldOp::Matches(regex) => {
                lhs.compile_with(move |x| regex.is_match(&cast_value!(x, Bytes)))
            }
            FieldOp::OneOf(values) => match values {
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

                    lhs.compile_with(move |x| match cast_value!(x, Ip) {
                        IpAddr::V4(addr) => v4.contains(&addr),
                        IpAddr::V6(addr) => v6.contains(&addr),
                    })
                }
                RhsValues::Int(values) => {
                    let values: RangeSet<_> = values.iter().cloned().collect();

                    lhs.compile_with(move |x| values.contains(&cast_value!(x, Int)))
                }
                RhsValues::Bytes(values) => {
                    let values: IndexSet<Box<[u8]>, FnvBuildHasher> =
                        values.into_iter().map(Into::into).collect();

                    lhs.compile_with(move |x| values.contains(&cast_value!(x, Bytes) as &[u8]))
                }
                RhsValues::Bool(_) => unreachable!(),
                RhsValues::Map(_) => unreachable!(),
                RhsValues::Array(_) => unreachable!(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        ast::function_expr::{FunctionCallArgExpr, FunctionCallExpr},
        execution_context::ExecutionContext,
        functions::{
            Function, FunctionArgKind, FunctionArgs, FunctionImpl, FunctionOptParam, FunctionParam,
        },
        rhs_types::IpRange,
        scheme::FieldIndex,
        types::{Array, Map},
    };
    use cidr::{Cidr, IpCidr};
    use lazy_static::lazy_static;
    use std::net::IpAddr;

    fn echo_function<'a>(args: FunctionArgs<'_, 'a>) -> LhsValue<'a> {
        args.next().unwrap()
    }

    fn lowercase_function<'a>(args: FunctionArgs<'_, 'a>) -> LhsValue<'a> {
        let input = args.next().unwrap();
        match input {
            LhsValue::Bytes(bytes) => LhsValue::Bytes(bytes.to_ascii_lowercase().into()),
            _ => panic!("Invalid type: expected Bytes, got {:?}", input),
        }
    }

    fn concat_function<'a>(args: FunctionArgs<'_, 'a>) -> LhsValue<'a> {
        let mut output = Vec::new();
        for (index, arg) in args.enumerate() {
            match arg {
                LhsValue::Bytes(bytes) => {
                    output.extend_from_slice(&bytes);
                }
                arg => panic!(
                    "Invalid type for argument {:?}: expected Bytes, got {:?}",
                    index, arg
                ),
            }
        }
        LhsValue::Bytes(output.into())
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
            };
            scheme
                .add_function(
                    "echo".into(),
                    Function {
                        params: vec![FunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Bytes,
                        implementation: FunctionImpl::new(echo_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "lowercase".into(),
                    Function {
                        params: vec![FunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Bytes,
                        implementation: FunctionImpl::new(lowercase_function),
                    },
                )
                .unwrap();
            scheme
                .add_function(
                    "concat".into(),
                    Function {
                        params: vec![],
                        opt_params: vec![
                            FunctionOptParam {
                                arg_kind: FunctionArgKind::Field,
                                default_value: "".into(),
                            },
                            FunctionOptParam {
                                arg_kind: FunctionArgKind::Literal,
                                default_value: "".into(),
                            },
                        ],
                        return_type: Type::Bytes,
                        implementation: FunctionImpl::new(concat_function),
                    },
                )
                .unwrap();
            scheme
        };
    }

    fn field(name: &'static str) -> Field<'static> {
        SCHEME.get_field_index(name).unwrap()
    }

    #[test]
    fn test_is_true() {
        let expr = assert_ok!(
            FieldExpr::lex_with("ssl", &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ssl")),
                    indexes: vec![],
                },
                op: FieldOp::IsTrue
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

        ctx.set_field_value("ssl", true).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ssl", false).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_ip_compare() {
        let expr = assert_ok!(
            FieldExpr::lex_with("ip.addr <= 10:20:30:40:50:60:70:80", &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ip.addr")),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value(
            "ip.addr",
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]),
        )
        .unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value(
            "ip.addr",
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x81]),
        )
        .unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_bytes_compare() {
        // just check that parsing doesn't conflict with IPv6
        {
            let expr = assert_ok!(
                FieldExpr::lex_with("http.host >= 10:20:30:40:50:60:70:80", &SCHEME),
                FieldExpr {
                    lhs: IndexExpr {
                        lhs: LhsFieldExpr::Field(field("http.host")),
                        indexes: vec![],
                    },
                    op: FieldOp::Ordering {
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
                FieldExpr::lex_with(r#"http.host < 12"#, &SCHEME),
                FieldExpr {
                    lhs: IndexExpr {
                        lhs: LhsFieldExpr::Field(field("http.host")),
                        indexes: vec![],
                    },
                    op: FieldOp::Ordering {
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
            FieldExpr::lex_with(r#"http.host == "example.org""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("http.host", "example.com").unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org").unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_bitwise_and() {
        let expr = assert_ok!(
            FieldExpr::lex_with("tcp.port & 1", &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: FieldOp::Int {
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

        ctx.set_field_value("tcp.port", 80).unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 443).unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_int_in() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port in { 80 443 2082..2083 }"#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: FieldOp::OneOf(RhsValues::Int(vec![80..=80, 443..=443, 2082..=2083])),
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

        ctx.set_field_value("tcp.port", 80).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 8080).unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 443).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 2081).unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 2082).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 2083).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 2084).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_bytes_in() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host in { "example.org" "example.com" }"#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: FieldOp::OneOf(RhsValues::Bytes(
                    ["example.org", "example.com",]
                        .iter()
                        .map(|&s| s.to_string().into())
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

        ctx.set_field_value("http.host", "example.com").unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.org").unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.net").unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_ip_in() {
        let expr = assert_ok!(
            FieldExpr::lex_with(
                r#"ip.addr in { 127.0.0.0/8 ::1 10.0.0.0..10.0.255.255 }"#,
                &SCHEME
            ),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("ip.addr")),
                    indexes: vec![],
                },
                op: FieldOp::OneOf(RhsValues::Ip(vec![
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

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 3]))
            .unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([255, 255, 255, 255]))
            .unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]))
            .unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 2]))
            .unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_contains_bytes() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host contains "abc""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: FieldOp::Contains("abc".to_owned().into())
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

        ctx.set_field_value("http.host", "example.org").unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "abc.net.au").unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_contains_str() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host contains 6F:72:67"#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.host")),
                    indexes: vec![],
                },
                op: FieldOp::Contains(vec![0x6F, 0x72, 0x67].into()),
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

        ctx.set_field_value("http.host", "example.com").unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org").unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_int_compare() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port < 8000"#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("tcp.port")),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("tcp.port", 80).unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 8080).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_array_contains_str() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.cookies[0] contains "abc""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.cookies")),
                    indexes: vec![FieldIndex::ArrayIndex(0)],
                },
                op: FieldOp::Contains("abc".to_owned().into()),
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "abc".into()).unwrap();
            arr
        });

        ctx.set_field_value("http.cookies", cookies).unwrap();
        assert_eq!(expr.execute(ctx), true);

        let cookies = LhsValue::Array({
            let mut arr = Array::new(Type::Bytes);
            arr.insert(0, "def".into()).unwrap();
            arr
        });

        ctx.set_field_value("http.cookies", cookies).unwrap();
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_map_of_bytes_contains_str() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.headers["host"] contains "abc""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::Field(field("http.headers")),
                    indexes: vec![FieldIndex::MapKey("host".to_string())],
                },
                op: FieldOp::Contains("abc".to_owned().into()),
            }
        );

        assert_json!(
            expr,
            {
                "lhs": ["http.headers", "host"],
                "op": "Contains",
                "rhs": "abc",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert("host".to_string(), "example.org".into())
                .unwrap();
            map
        });

        ctx.set_field_value("http.headers", headers).unwrap();
        assert_eq!(expr.execute(ctx), false);

        let headers = LhsValue::Map({
            let mut map = Map::new(Type::Bytes);
            map.insert("host".to_string(), "abc.net.au".into()).unwrap();
            map
        });

        ctx.set_field_value("http.headers", headers).unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_echo_function() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"echo(http.host) == "example.org""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("echo"),
                        function: SCHEME.get_function("echo").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                    }),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("http.host", "example.com").unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org").unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_lowercase_function() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"lowercase(http.host) == "example.org""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("lowercase"),
                        function: SCHEME.get_function("lowercase").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                    }),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("http.host", "EXAMPLE.COM").unwrap();
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "EXAMPLE.ORG").unwrap();
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_bytes_compare_with_concat_function() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"concat(http.host) == "example.org""#, &SCHEME),
            FieldExpr {
                lhs: IndexExpr {
                    lhs: LhsFieldExpr::FunctionCallExpr(FunctionCallExpr {
                        name: String::from("concat"),
                        function: SCHEME.get_function("concat").unwrap(),
                        args: vec![FunctionCallArgExpr::IndexExpr(IndexExpr {
                            lhs: LhsFieldExpr::Field(field("http.host")),
                            indexes: vec![],
                        })],
                    }),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("http.host", "example.org").unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.co.uk").unwrap();
        assert_eq!(expr.execute(ctx), false);

        let expr = assert_ok!(
            FieldExpr::lex_with(r#"concat(http.host, ".org") == "example.org""#, &SCHEME),
            FieldExpr {
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
                    }),
                    indexes: vec![],
                },
                op: FieldOp::Ordering {
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

        ctx.set_field_value("http.host", "example").unwrap();
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "cloudflare").unwrap();
        assert_eq!(expr.execute(ctx), false);
    }
}
