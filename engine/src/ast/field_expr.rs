use super::Expr;
use execution_context::ExecutionContext;
use lex::{skip_space, span, Lex, LexErrorKind, LexResult, LexWith};
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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
enum FieldOp {
    Ordering(OrderingOp, RhsValue),
    Unsigned(UnsignedOp, u64),
    Matches(Regex),
    OneOf(RhsValues),
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FieldExpr<'s> {
    field: Field<'s>,
    op: FieldOp,
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FieldExpr<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        let (field, input) = Field::lex_with(input, scheme)?;
        let field_type = field.get_type();

        let (op, input) = if field_type == Type::Bool {
            (
                FieldOp::Ordering(OrderingOp::Equal, RhsValue::Bool(true)),
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
                (_, ComparisonOp::Ordering(mask)) => {
                    let (rhs, input) = RhsValue::lex_with(input, field_type)?;
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
                            let regex = Regex::try_from(&rhs).map_err(|err| {
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
    use cidr::{Cidr, IpCidr};
    use std::{net::IpAddr, ops::RangeInclusive};

    fn cidr<A: Into<IpAddr>>(addr: A, len: u8) -> RangeInclusive<IpAddr> {
        let cidr = IpCidr::new(addr.into(), len).unwrap();
        cidr.first_address()..=cidr.last_address()
    }

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
                op: FieldOp::Ordering(OrderingOp::Equal, RhsValue::Bool(true))
            }
        );

        ctx.set_field_value("ssl", true);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ssl", false);
        assert_eq!(expr.execute(ctx), false);
    }

    {
        let expr = assert_ok!(
            FieldExpr::lex_with("ip.addr >= 10:20:30:40:50:60:70:80", scheme),
            FieldExpr {
                field: field("ip.addr"),
                op: FieldOp::Ordering(
                    OrderingOp::GreaterThanEqual,
                    RhsValue::Ip(IpAddr::from([
                        0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80
                    ]))
                ),
            }
        );

        ctx.set_field_value("ip.addr", IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]));
        assert_eq!(expr.execute(ctx), false);

        ctx.set_field_value(
            "ip.addr",
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80]),
        );
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value(
            "ip.addr",
            IpAddr::from([0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x81]),
        );
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("ip.addr", IpAddr::from([127, 0, 0, 1]));
        assert_eq!(expr.execute(ctx), false);
    }

    assert_ok!(
        FieldExpr::lex_with("http.host >= 10:20:30:40:50:60:70:80", scheme),
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
            FieldExpr::lex_with("tcp.port & 1", scheme),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Unsigned(UnsignedOp::BitwiseAnd, 1),
            }
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
                op: FieldOp::Ordering(
                    OrderingOp::Equal,
                    RhsValue::Bytes("example.org".to_owned().into())
                )
            }
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
                        cidr([127, 0, 0, 0], 8),
                        cidr([0, 0, 0, 0, 0, 0, 0, 1], 128),
                        cidr([10, 0, 0, 0], 16),
                    ].into()
                )),
            }
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
                op: FieldOp::Matches(Regex::new(r#"\x61\x62\x63"#).unwrap())
            }
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
                op: FieldOp::Matches(Regex::new(r#"\x6F\x72\x67"#).unwrap())
            }
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
            op: FieldOp::Ordering(OrderingOp::LessThan, RhsValue::Bytes(vec![0x12].into())),
        }
    );

    {
        let expr = assert_ok!(
            FieldExpr::lex_with(r#"tcp.port < 8000"#, scheme),
            FieldExpr {
                field: field("tcp.port"),
                op: FieldOp::Ordering(OrderingOp::LessThan, RhsValue::Unsigned(8000)),
            }
        );

        ctx.set_field_value("tcp.port", 80);
        assert_eq!(expr.execute(ctx), true);

        ctx.set_field_value("tcp.port", 8080);
        assert_eq!(expr.execute(ctx), false);
    }
}
