mod contains_op;

use self::contains_op::ContainsOp;
use super::Expr;
use execution_context::ExecutionContext;
use lex::{skip_space, span, Lex, LexErrorKind, LexResult, LexWith};
use memmem::Searcher;
use rhs_types::{Bytes, Regex};
use scheme::{Field, Scheme};
use std::cmp::Ordering;
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

lex_enum!(UnsignedOp {
    "&" | "bitwise_and" => BitwiseAnd,
});

lex_enum!(BytesOp {
    "contains" => Contains,
    "~" | "matches" => Matches,
});

lex_enum!(ComparisonOp {
    "in" => In,
    OrderingOp => Ordering,
    UnsignedOp => Unsigned,
    BytesOp => Bytes,
});

#[derive(Debug, PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
enum FieldOp {
    Ordering {
        op: OrderingOp,
        rhs: RhsValue,
    },

    Unsigned {
        op: UnsignedOp,
        rhs: u64,
    },

    #[serde(serialize_with = "serialize_contains")]
    Contains(ContainsOp),

    #[serde(serialize_with = "serialize_matches")]
    Matches(Regex),

    #[serde(serialize_with = "serialize_one_of")]
    OneOf(RhsValues),
}

fn serialize_op_rhs<T: ::serde::Serialize, S: ::serde::Serializer>(
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

fn serialize_contains<S: ::serde::Serializer>(rhs: &ContainsOp, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Contains", rhs, ser)
}

fn serialize_matches<S: ::serde::Serializer>(rhs: &Regex, ser: S) -> Result<S::Ok, S::Error> {
    serialize_op_rhs("Matches", rhs, ser)
}

fn serialize_one_of<S: ::serde::Serializer>(rhs: &RhsValues, ser: S) -> Result<S::Ok, S::Error> {
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
            (
                FieldOp::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bool(true),
                },
                input,
            )
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
                (Type::Unsigned, ComparisonOp::Unsigned(op)) => {
                    let (rhs, input) = u64::lex(input)?;
                    (FieldOp::Unsigned { op, rhs }, input)
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                    BytesOp::Contains => {
                        let (bytes, input) = Bytes::lex(input)?;
                        (FieldOp::Contains(bytes.into()), input)
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

    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        macro_rules! cast_field {
            ($field:ident, $lhs:ident, $ty:ident) => {
                match $lhs {
                    LhsValue::$ty(value) => value,
                    _ => unreachable!(),
                }
            };
        }

        let lhs = ctx.get_field_value_unchecked(self.field);

        match &self.op {
            FieldOp::Ordering { op, rhs } => op.matches_opt(lhs.partial_cmp(rhs)),
            FieldOp::Unsigned {
                op: UnsignedOp::BitwiseAnd,
                rhs,
            } => cast_field!(field, lhs, Unsigned) & rhs != 0,
            FieldOp::Contains(op) => op.search_in(cast_field!(field, lhs, Bytes)).is_some(),
            FieldOp::Matches(regex) => regex.is_match(cast_field!(field, lhs, Bytes)),
            FieldOp::OneOf(values) => values.contains(lhs),
        }
    }
}

#[test]
fn test() {
    use serde_json::to_value as json;
    use std::net::IpAddr;

    let scheme: &Scheme = &[
        ("http.host", Type::Bytes),
        ("ip.addr", Type::Ip),
        ("ssl", Type::Bool),
        ("tcp.port", Type::Unsigned),
    ]
        .iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    let field = |name| scheme.get_field_index(name).unwrap();

    let ctx = &mut ExecutionContext::new(scheme);

    {
        let expr = assert_ok!(
            FieldExpr::lex_with("ssl", scheme),
            FieldExpr {
                field: field("ssl"),
                op: FieldOp::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bool(true)
                }
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "ssl",
                "op": "Equal",
                "rhs": true
            })
        );

        ctx.set_field_value("ssl", true);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ssl", false);
        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex_with("ip.addr <= 10:20:30:40:50:60:70:80", scheme),
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

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "ip.addr",
                "op": "LessThanEqual",
                "rhs": "10:20:30:40:50:60:70:80"
            })
        );

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

    assert_ok!(
        FieldExpr::lex_with("http.host >= 10:20:30:40:50:60:70:80", scheme),
        FieldExpr {
            field: field("http.host"),
            op: FieldOp::Ordering {
                op: OrderingOp::GreaterThanEqual,
                rhs: RhsValue::Bytes(vec![0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into()),
            },
        }
    );

    {
        let expr = assert_ok!(
            FieldExpr::lex_with("tcp.port & 1", scheme),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Unsigned {
                    op: UnsignedOp::BitwiseAnd,
                    rhs: 1,
                }
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "tcp.port",
                "op": "BitwiseAnd",
                "rhs": 1
            })
        );

        ctx.set_field_value("tcp.port", 80);
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", 443);
        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host == "example.org""#, scheme),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Ordering {
                    op: OrderingOp::Equal,
                    rhs: RhsValue::Bytes("example.org".to_owned().into())
                }
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "http.host",
                "op": "Equal",
                // strings are currently encoded as a JSON arrays of bytes
                "rhs": b"example.org"
            })
        );

        ctx.set_field_value("http.host", "example.com");
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port in { 80 443 2082..2083 }"#, scheme),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::OneOf(RhsValues::Unsigned(
                    vec![80..=80, 443..=443, 2082..=2083].into()
                )),
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "tcp.port",
                "op": "OneOf",
                "rhs": [
                    { "start": 80, "end": 80 },
                    { "start": 443, "end": 443 },
                    { "start": 2082, "end": 2083 },
                ]
            })
        );

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

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host in { "example.org" "example.com" }"#, scheme),
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

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "http.host",
                "op": "OneOf",
                // strings are currently encoded as a JSON arrays of bytes
                "rhs": [
                    b"example.org",
                    b"example.com",
                ]
            })
        );

        ctx.set_field_value("http.host", "example.com");
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", "example.net");
        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(
                r#"ip.addr in { 127.0.0.0/8 ::1 10.0.0.0..10.0.255.255 }"#,
                scheme
            ),
            FieldExpr {
                field: field("ip.addr"),
                op: FieldOp::OneOf(RhsValues::Ip(
                    vec![
                        IpAddr::from([127, 0, 0, 0])..=IpAddr::from([127, 255, 255, 255]),
                        IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1])
                            ..=IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]),
                        IpAddr::from([10, 0, 0, 0])..=IpAddr::from([10, 0, 255, 255]),
                    ].into()
                )),
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "ip.addr",
                "op": "OneOf",
                "rhs": [
                    { "start": "127.0.0.0", "end": "127.255.255.255" },
                    { "start": "::1", "end": "::1" },
                    { "start": "10.0.0.0", "end": "10.0.255.255" },
                ]
            })
        );

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

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host contains "abc""#, scheme),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Contains("abc".to_owned().into())
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "http.host",
                "op": "Contains",
                // strings are currently encoded as a JSON arrays of bytes
                "rhs": b"abc",
            })
        );

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "abc.net.au");
        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"http.host contains 6F:72:67"#, scheme),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Contains(vec![0x6F, 0x72, 0x67].into()),
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "http.host",
                "op": "Contains",
                "rhs": [0x6F, 0x72, 0x67],
            })
        );

        ctx.set_field_value("http.host", "example.com");
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", "example.org");
        assert_eq!(expr.execute(ctx), true);
    }

    assert_ok!(
        FieldExpr::lex_with(r#"http.host < 12"#, scheme),
        FieldExpr {
            field: field("http.host"),
            op: FieldOp::Ordering {
                op: OrderingOp::LessThan,
                rhs: RhsValue::Bytes(vec![0x12].into()),
            },
        }
    );

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port < 8000"#, scheme),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Ordering {
                    op: OrderingOp::LessThan,
                    rhs: RhsValue::Unsigned(8000)
                },
            }
        );

        assert_eq!(
            json(&expr).unwrap(),
            json!({
                "field": "tcp.port",
                "op": "LessThan",
                "rhs": 8000,
            })
        );

        ctx.set_field_value("tcp.port", 80);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 8080);
        assert_eq!(expr.execute(ctx), false);
    }
}
