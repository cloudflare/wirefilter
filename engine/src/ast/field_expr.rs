use super::{Expr, Filter};
use fnv::FnvBuildHasher;
use heap_searcher::HeapSearcher;
use indexmap::IndexSet;
use lex::{skip_space, span, Lex, LexErrorKind, LexResult, LexWith};
use memmem::Searcher;
use range_set::RangeSet;
use rhs_types::{Bytes, ExplicitIpRange, Regex};
use scheme::{Field, Scheme};
use serde::{Serialize, Serializer};
use std::{cmp::Ordering, net::IpAddr};
use strict_partial_ord::StrictPartialOrd;
use types::{GetType, LhsValue, RhsValue, RhsValues, Type};

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
pub struct FieldExpr<'s> {
    field: Field<'s>,

    #[serde(flatten)]
    op: FieldOp,
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FieldExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        let (field, input) = Field::lex_with(input, scheme)?;
        let field_type = field.get_type();

        let (op, input) = if field_type == Type::Bool {
            (FieldOp::IsTrue, input)
        } else {
            let (op, input) = ComparisonOp::lex(skip_space(input))?;

            let input_after_op = input;

            let input = skip_space(input);

            match (field_type, op) {
                (_, ComparisonOp::In) => {
                    let (rhs, input) = RhsValues::lex_with(input, field_type)?;
                    (FieldOp::OneOf(rhs), input)
                }
                (_, ComparisonOp::Ordering(op)) => {
                    let (rhs, input) = RhsValue::lex_with(input, field_type)?;
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
                        LexErrorKind::UnsupportedOp { field_type },
                        span(initial_input, input_after_op),
                    ));
                }
            }
        };

        Ok((FieldExpr { field, op }, input))
    }
}

impl<'s> Expr<'s> for FieldExpr<'s> {
    fn uses(&self, field: Field<'s>) -> bool {
        self.field == field
    }

    fn compile(self) -> Filter<'s> {
        macro_rules! cast {
            ($lhs:expr, $ty:ident) => {
                match $lhs {
                    LhsValue::$ty(value) => value,
                    _ => unreachable!(),
                }
            };
        }

        let field = self.field;

        match self.op {
            FieldOp::IsTrue => {
                Filter::new(move |ctx| *cast!(ctx.get_field_value_unchecked(field), Bool))
            }
            FieldOp::Ordering { op, rhs } => Filter::new(move |ctx| {
                op.matches_opt(
                    ctx.get_field_value_unchecked(field)
                        .strict_partial_cmp(&rhs),
                )
            }),
            FieldOp::Int {
                op: IntOp::BitwiseAnd,
                rhs,
            } => {
                Filter::new(move |ctx| cast!(ctx.get_field_value_unchecked(field), Int) & rhs != 0)
            }
            FieldOp::Contains(bytes) => {
                let searcher = HeapSearcher::from(bytes);

                Filter::new(move |ctx| {
                    searcher
                        .search_in(cast!(ctx.get_field_value_unchecked(field), Bytes))
                        .is_some()
                })
            }
            FieldOp::Matches(regex) => Filter::new(move |ctx| {
                regex.is_match(cast!(ctx.get_field_value_unchecked(field), Bytes))
            }),
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
                    Filter::new(
                        move |ctx| match cast!(ctx.get_field_value_unchecked(field), Ip) {
                            IpAddr::V4(addr) => v4.contains(addr),
                            IpAddr::V6(addr) => v6.contains(addr),
                        },
                    )
                }
                RhsValues::Int(values) => {
                    let values: RangeSet<_> = values.iter().cloned().collect();
                    Filter::new(move |ctx| {
                        values.contains(cast!(ctx.get_field_value_unchecked(field), Int))
                    })
                }
                RhsValues::Bytes(values) => {
                    let values: IndexSet<Box<[u8]>, FnvBuildHasher> =
                        values.into_iter().map(|value| value.into()).collect();

                    Filter::new(move |ctx| {
                        values.contains(cast!(ctx.get_field_value_unchecked(field), Bytes) as &[u8])
                    })
                }
                RhsValues::Bool(_) => unreachable!(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cidr::{Cidr, IpCidr};
    use execution_context::ExecutionContext;
    use lazy_static::lazy_static;
    use rhs_types::IpRange;
    use std::net::IpAddr;

    lazy_static! {
        static ref SCHEME: Scheme = [
            ("http.host", Type::Bytes),
            ("ip.addr", Type::Ip),
            ("ssl", Type::Bool),
            ("tcp.port", Type::Int),
        ]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();
    }

    fn field(name: &'static str) -> Field<'static> {
        SCHEME.get_field_index(name).unwrap()
    }

    #[test]
    fn test_is_true() {
        let expr = assert_ok!(
            FieldExpr::lex_with("ssl", &SCHEME),
            FieldExpr {
                field: field("ssl"),
                op: FieldOp::IsTrue
            }
        );

        assert_json!(
            expr,
            {
                "field": "ssl",
                "op": "IsTrue"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("ssl", true);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ssl", false);
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_ip_compare() {
        let expr = assert_ok!(
            FieldExpr::lex_with("ip.addr <= 10:20:30:40:50:60:70:80", &SCHEME),
            FieldExpr {
                field: field("ip.addr"),
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
                "field": "ip.addr",
                "op": "LessThanEqual",
                "rhs": "10:20:30:40:50:60:70:80"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value(
            "ip.addr",
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]),
        );
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value(
            "ip.addr",
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x81]),
        );
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 1]));
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_bytes_compare() {
        // just check that parsing doesn't conflict with IPv6
        {
            let expr = assert_ok!(
                FieldExpr::lex_with("http.host >= 10:20:30:40:50:60:70:80", &SCHEME),
                FieldExpr {
                    field: field("http.host"),
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
                    "field": "http.host",
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
                    field: field("http.host"),
                    op: FieldOp::Ordering {
                        op: OrderingOp::LessThan,
                        rhs: RhsValue::Bytes(vec![0x12].into()),
                    },
                }
            );

            assert_json!(
                expr,
                {
                    "field": "http.host",
                    "op": "LessThan",
                    "rhs": [0x12]
                }
            );
        }

        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host == "example.org""#, &SCHEME),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_json!(
            expr,
            {
                "field": "http.host",
                "op": "Equal",
                "rhs": "example.org"
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("http.host", "example.com");
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_bitwise_and() {
        let expr = assert_ok!(
            FieldExpr::lex_with("tcp.port & 1", &SCHEME),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Int {
                    op: IntOp::BitwiseAnd,
                    rhs: 1,
                }
            }
        );

        assert_json!(
            expr,
            {
                "field": "tcp.port",
                "op": "BitwiseAnd",
                "rhs": 1
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("tcp.port", 80);
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 443);
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_int_in() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port in { 80 443 2082..2083 }"#, &SCHEME),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::OneOf(RhsValues::Int(vec![80..=80, 443..=443, 2082..=2083])),
            }
        );

        assert_json!(
            expr,
            {
                "field": "tcp.port",
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

        ctx.set_field_value("tcp.port", 80);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 8080);
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 443);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 2081);
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 2082);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 2083);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 2084);
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_bytes_in() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host in { "example.org" "example.com" }"#, &SCHEME),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::OneOf(RhsValues::Bytes(
                    ["example.org", "example.com",]
                        .iter()
                        .map(|s| s.to_string().into())
                        .collect()
                )),
            }
        );

        assert_json!(
            expr,
            {
                "field": "http.host",
                "op": "OneOf",
                "rhs": [
                    "example.org",
                    "example.com",
                ]
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("http.host", "example.com");
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.net");
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
                field: field("ip.addr"),
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
                "field": "ip.addr",
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

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 1]));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 3]));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([255, 255, 255, 255]));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 2]));
        assert_eq!(expr.execute(ctx), false);
    }

    #[test]
    fn test_contains_bytes() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host contains "abc""#, &SCHEME),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Contains("abc".to_owned().into())
            }
        );

        assert_json!(
            expr,
            {
                "field": "http.host",
                "op": "Contains",
                "rhs": "abc",
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "abc.net.au");
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_contains_str() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host contains 6F:72:67"#, &SCHEME),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Contains(vec![0x6F, 0x72, 0x67].into()),
            }
        );

        assert_json!(
            expr,
            {
                "field": "http.host",
                "op": "Contains",
                "rhs": [0x6F, 0x72, 0x67],
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("http.host", "example.com");
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), true);
    }

    #[test]
    fn test_int_compare() {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port < 8000"#, &SCHEME),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Ordering {
                    op: OrderingOp::LessThan,
                    rhs: RhsValue::Int(8000)
                },
            }
        );

        assert_json!(
            expr,
            {
                "field": "tcp.port",
                "op": "LessThan",
                "rhs": 8000,
            }
        );

        let expr = expr.compile();
        let ctx = &mut ExecutionContext::new(&SCHEME);

        ctx.set_field_value("tcp.port", 80);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 8080);
        assert_eq!(expr.execute(ctx), false);
    }
}
