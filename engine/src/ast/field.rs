use super::Expr;
use execution_context::ExecutionContext;
use lex::{span, Lex, LexErrorKind, LexResult};
use rhs_types::{Bytes, Regex};
use scheme::{FieldIndex, Scheme};
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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum FieldOp {
    Ordering(OrderingOp, RhsValue),
    Unsigned(UnsignedOp, u64),
    Matches(Regex),
    OneOf(RhsValues),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FieldExpr<'s> {
    field: FieldIndex<'s>,
    op: FieldOp,
}

impl<'s> Expr<'s> for FieldExpr<'s> {
    fn uses(&self, field: FieldIndex<'s>) -> bool {
        self.field == field
    }

    fn lex<'i>(scheme: &'s Scheme, input: &'i str) -> LexResult<'i, Self> {
        let initial_input = input;

        let (field, input) = FieldIndex::lex(scheme, input)?;
        let field_type = field.get_type();

        let (op, input) = if field_type == Type::Bool {
            (
                FieldOp::Ordering(OrderingOp::Equal, RhsValue::Bool(true)),
                input,
            )
        } else {
            let (op, input) = ComparisonOp::lex(input.trim_left())?;

            let input_after_op = input;

            let input = input.trim_left();

            match (field_type, op) {
                (_, ComparisonOp::In) => {
                    let (rhs, input) = RhsValues::lex(input, field_type)?;
                    (FieldOp::OneOf(rhs), input)
                }
                (_, ComparisonOp::Ordering(mask)) => {
                    let (rhs, input) = RhsValue::lex(input, field_type)?;
                    (FieldOp::Ordering(mask, rhs), input)
                }
                (Type::Unsigned, ComparisonOp::Unsigned(op)) => {
                    let (rhs, input) = u64::lex(input)?;
                    (FieldOp::Unsigned(op, rhs), input)
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => {
                    let (regex, input) = match op {
                        BytesOp::Contains => {
                            let input_before_rhs = input;
                            let (rhs, input) = Bytes::lex(input)?;
                            let regex = Regex::try_from(rhs).map_err(|err| {
                                // This is very, very, very unlikely as we're just converting
                                // a literal into a regex and not using any repetitions etc.,
                                // but better to be safe than sorry and report such error.
                                (LexErrorKind::ParseRegex(err), span(input_before_rhs, input))
                            })?;
                            (regex, input)
                        }
                        BytesOp::Matches => Regex::lex(input)?,
                    };
                    (FieldOp::Matches(regex), input)
                }
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

    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        macro_rules! cast_field {
            ($field:ident, $lhs:ident, $ty:ident) => {
                match $lhs {
                    LhsValue::$ty(value) => value,
                    _ => unreachable!(),
                }
            };
        }

        // this is safe because this code is reachable only from Filter::execute
        // which already performs the scheme compatibility check
        let lhs = ctx.get_field_value_unchecked(self.field.index());

        match &self.op {
            FieldOp::Ordering(op, rhs) => op.matches_opt(lhs.partial_cmp(rhs)),
            FieldOp::Unsigned(UnsignedOp::BitwiseAnd, rhs) => {
                cast_field!(field, lhs, Unsigned) & rhs != 0
            }
            FieldOp::Matches(regex) => regex.is_match(cast_field!(field, lhs, Bytes)),
            FieldOp::OneOf(values) => values.contains(lhs),
        }
    }
}

#[test]
fn test() {
    use cidr::{Cidr, Ipv4Cidr, Ipv6Cidr};

    let scheme: &Scheme = &[
        ("http.host", Type::Bytes),
        ("ip.addr", Type::Ip),
        ("ssl", Type::Bool),
        ("tcp.port", Type::Unsigned),
    ].iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    let field = |name| scheme.get_field_index(name).unwrap();

    let ctx = &mut ExecutionContext::new(scheme);

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, "ssl"),
            FieldExpr {
                field: field("ssl"),
                op: FieldOp::Ordering(OrderingOp::Equal, RhsValue::Bool(true))
            }
        );

        ctx.set_field_value("ssl", LhsValue::Bool(true));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ssl", LhsValue::Bool(false));
        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, "ip.addr >= 10:20:30:40:50:60:70:80"),
            FieldExpr {
                field: field("ip.addr"),
                op: FieldOp::Ordering(
                    OrderingOp::GreaterThanEqual,
                    RhsValue::Ip(
                        Ipv6Cidr::new_host([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into())
                            .into()
                    )
                ),
            }
        );

        ctx.set_field_value("ip.addr", LhsValue::Ip([0, 0, 0, 0, 0, 0, 0, 1].into()));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value(
            "ip.addr",
            LhsValue::Ip([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into()),
        );
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value(
            "ip.addr",
            LhsValue::Ip([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x81].into()),
        );
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", LhsValue::Ip([127, 0, 0, 1].into()));
        assert_eq!(expr.execute(ctx), false);
    }

    assert_ok!(
        FieldExpr::lex(scheme, "http.host >= 10:20:30:40:50:60:70:80"),
        FieldExpr {
            field: field("http.host"),
            op: FieldOp::Ordering(
                OrderingOp::GreaterThanEqual,
                RhsValue::Bytes(vec![0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80].into())
            ),
        }
    );

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, "tcp.port & 1"),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Unsigned(UnsignedOp::BitwiseAnd, 1),
            }
        );

        ctx.set_field_value("tcp.port", LhsValue::Unsigned(80));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("tcp.port", LhsValue::Unsigned(443));
        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, r#"http.host == "example.org""#),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Ordering(
                    OrderingOp::Equal,
                    RhsValue::Bytes("example.org".to_owned().into())
                )
            }
        );

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.com"[..].into()));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.org"[..].into()));
        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, r#"http.host in { "example.org" "example.com" }"#),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::OneOf(RhsValues::Bytes(vec![
                    "example.org".to_owned().into(),
                    "example.com".to_owned().into(),
                ])),
            }
        );

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.com"[..].into()));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.org"[..].into()));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.net"[..].into()));
        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, r#"ip.addr in { 127.0.0.0/8 ::1 }"#),
            FieldExpr {
                field: field("ip.addr"),
                op: FieldOp::OneOf(RhsValues::Ip(vec![
                    Ipv4Cidr::new([127, 0, 0, 0].into(), 8).unwrap().into(),
                    Ipv6Cidr::new_host(1.into()).into(),
                ])),
            }
        );

        ctx.set_field_value("ip.addr", LhsValue::Ip([127, 0, 0, 1].into()));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", LhsValue::Ip([127, 0, 0, 3].into()));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", LhsValue::Ip([255, 255, 255, 255].into()));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("ip.addr", LhsValue::Ip([0, 0, 0, 0, 0, 0, 0, 1].into()));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", LhsValue::Ip([0, 0, 0, 0, 0, 0, 0, 2].into()));
        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, r#"http.host contains "abc""#),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Matches(Regex::new(r#"(?u)abc"#).unwrap())
            }
        );

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.org"[..].into()));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", LhsValue::Bytes(b"abc.net.au"[..].into()));
        assert_eq!(expr.execute(ctx), true);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, r#"http.host contains 6F:72:67"#),
            FieldExpr {
                field: field("http.host"),
                op: FieldOp::Matches(Regex::new(r#"\x6F\x72\x67"#).unwrap())
            }
        );

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.com"[..].into()));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value("http.host", LhsValue::Bytes(b"example.org"[..].into()));
        assert_eq!(expr.execute(ctx), true);
    }

    assert_ok!(
        FieldExpr::lex(scheme, r#"http.host < 12"#),
        FieldExpr {
            field: field("http.host"),
            op: FieldOp::Ordering(OrderingOp::LessThan, RhsValue::Bytes(vec![0x12].into())),
        }
    );

    {
        let expr = assert_ok!(
            FieldExpr::lex(scheme, r#"tcp.port < 8000"#),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Ordering(OrderingOp::LessThan, RhsValue::Unsigned(8000)),
            }
        );

        ctx.set_field_value("tcp.port", LhsValue::Unsigned(80));
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", LhsValue::Unsigned(8080));
        assert_eq!(expr.execute(ctx), false);
    }
}
