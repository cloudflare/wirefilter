use bytes::Bytes;
use field::Field;
use filter::{Filter, FilterOp};
use fnv::FnvBuildHasher;
use indexmap::IndexMap;
use lex::{expect, span, Lex, LexError, LexErrorKind, LexResult};
use op::{BytesOp, CombiningOp, ComparisonOp, OrderingOp, UnaryOp};
use re::Regex;
use types::{GetType, RhsValue, RhsValues, Type};

use std::borrow::Borrow;
use std::iter::FromIterator;

#[derive(Default)]
pub struct Scheme {
    fields: IndexMap<String, Type, FnvBuildHasher>,
}

impl FromIterator<(String, Type)> for Scheme {
    fn from_iter<I: IntoIterator<Item = (String, Type)>>(iter: I) -> Self {
        Scheme {
            fields: IndexMap::from_iter(iter),
        }
    }
}

fn combining_op(input: &str) -> (Option<CombiningOp>, &str) {
    match CombiningOp::lex(input) {
        Ok((op, input)) => (Some(op), input.trim_left()),
        Err(_) => (None, input),
    }
}

impl<'s> Scheme {
    fn simple_filter<'i>(&'s self, input: &'i str) -> LexResult<'i, Filter<'s>> {
        if let Ok((op, input)) = UnaryOp::lex(input) {
            let input = input.trim_left();
            let (arg, input) = self.simple_filter(input)?;
            return Ok((Filter::Unary(op, Box::new(arg)), input.trim_left()));
        }

        if let Ok(input) = expect(input, "(") {
            let input = input.trim_left();
            let (res, input) = self.combined_filter(input)?;
            let input = input.trim_left();
            let input = expect(input, ")")?;
            return Ok((res, input.trim_left()));
        }

        let initial_input = input;

        let (lhs, input) = Field::lex(input)?;

        let (_, lhs, lhs_type) = self
            .fields
            .get_full(lhs.path())
            .ok_or_else(|| (LexErrorKind::UnknownField, lhs.path()))?;

        let lhs = Field::new(lhs.borrow());
        let lhs_type = lhs_type.get_type();

        let input = input.trim_left();

        if lhs_type == Type::Bool {
            return Ok((
                Filter::Op(
                    lhs,
                    FilterOp::Ordering(OrderingOp::Equal, RhsValue::Bool(true)),
                ),
                input,
            ));
        }

        let (op, input) = if let Ok(input) = expect(input, "in") {
            let input = input.trim_left();

            let (values, input) = RhsValues::lex(input, lhs_type)?;

            (FilterOp::OneOf(values), input)
        } else {
            let (op, input) = ComparisonOp::lex(input)?;

            let input = input.trim_left();

            let (filter, input) = match (lhs_type, op) {
                (_, ComparisonOp::Ordering(mask)) => {
                    let (rhs, input) = RhsValue::lex(input, lhs_type)?;
                    (FilterOp::Ordering(mask, rhs), input)
                }
                (Type::Unsigned, ComparisonOp::Unsigned(op)) => {
                    let (rhs, input) = u64::lex(input)?;
                    (FilterOp::Unsigned(op, rhs), input)
                }
                (Type::Bytes, ComparisonOp::Bytes(op)) => {
                    let (regex, input) = match op {
                        BytesOp::Contains => {
                            let (rhs, input) = Bytes::lex(input)?;
                            (Regex::from(rhs), input)
                        }
                        BytesOp::Matches => Regex::lex(input)?,
                    };
                    (FilterOp::Matches(regex), input)
                }
                (lhs, op) => {
                    return Err((
                        LexErrorKind::UnsupportedOp { lhs, op },
                        span(initial_input, input),
                    ))
                }
            };

            (filter, input.trim_left())
        };

        Ok((Filter::Op(lhs, op), input))
    }

    fn filter_prec<'i>(
        &'s self,
        mut lhs: Filter<'s>,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Filter<'s>> {
        while let Some(op) = lookahead.0 {
            let mut rhs = self.simple_filter(lookahead.1)?;
            loop {
                lookahead = combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = self.filter_prec(rhs.0, lookahead.0, lookahead)?;
            }
            match lhs {
                Filter::Combine(lhs_op, ref mut filters) if lhs_op == op => {
                    filters.push(rhs.0);
                }
                _ => {
                    lhs = Filter::Combine(op, vec![lhs, rhs.0]);
                }
            }
            if lookahead.0 < min_prec {
                // pretend we haven't seen an operator if its precedence is
                // outside of our limits
                lookahead = (None, rhs.1);
            }
        }
        Ok((lhs, lookahead.1))
    }

    fn combined_filter<'i>(&'s self, input: &'i str) -> LexResult<'i, Filter<'s>> {
        let (lhs, input) = self.simple_filter(input)?;
        let lookahead = combining_op(input);
        self.filter_prec(lhs, None, lookahead)
    }

    pub fn add_field(&mut self, name: String, ty: Type) {
        self.fields.insert(name, ty);
    }

    pub fn parse<'i>(&'s self, input: &'i str) -> Result<Filter<'s>, LexError<'i>> {
        let (res, input) = self.combined_filter(input)?;
        if input.is_empty() {
            Ok(res)
        } else {
            Err((LexErrorKind::EOF, input))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use cidr::{Cidr, IpCidr, Ipv4Cidr, Ipv6Cidr};
    use std::net::{Ipv4Addr, Ipv6Addr};

    #[test]
    fn parse() {
        let context: Scheme = [
            ("http.host", Type::Bytes),
            ("port", Type::Unsigned),
            ("ip.src", Type::Ip),
            ("isTCP", Type::Bool),
        ].iter()
            .map(|&(k, t)| (k.to_owned(), t))
            .collect();

        assert_eq!(
            context.parse(
                r#"http.host contains "t" or http.host contains E0:BE or http.host matches "^\d+""#
            ),
            Ok(Filter::Combine(
                CombiningOp::Or,
                vec![
                    Filter::Op(
                        Field::new("http.host"),
                        FilterOp::Matches(Regex::new(r"(?u)t").unwrap()),
                    ),
                    Filter::Op(
                        Field::new("http.host"),
                        FilterOp::Matches(Regex::new(r"\xE0\xBE").unwrap()),
                    ),
                    Filter::Op(
                        Field::new("http.host"),
                        FilterOp::Matches(Regex::new(r"^\d+").unwrap()),
                    ),
                ]
            ))
        );
        assert_eq!(
            context.parse("port in { 80 443 }"),
            Ok(Filter::Op(
                Field::new("port"),
                FilterOp::OneOf(RhsValues::Unsigned(vec![80, 443]))
            ))
        );
        assert_eq!(
            context.parse(
                "not ip.src in { 127.0.0.0/8 ::1/128 } and (port == 80) and !isTCP or port >= 1024"
            ),
            Ok(Filter::Combine(
                CombiningOp::Or,
                vec![
                    Filter::Combine(
                        CombiningOp::And,
                        vec![
                            Filter::Unary(
                                UnaryOp::Not,
                                Box::new(Filter::Op(
                                    Field::new("ip.src"),
                                    FilterOp::OneOf(RhsValues::Ip(vec![
                                        IpCidr::V4(
                                            Ipv4Cidr::new(Ipv4Addr::new(127, 0, 0, 0), 8).unwrap(),
                                        ).into(),
                                        IpCidr::V6(Ipv6Cidr::new(Ipv6Addr::from(1), 128).unwrap())
                                            .into(),
                                    ])),
                                )),
                            ),
                            Filter::Op(
                                Field::new("port"),
                                FilterOp::Ordering(OrderingOp::Equal, RhsValue::Unsigned(80)),
                            ),
                            Filter::Unary(
                                UnaryOp::Not,
                                Box::new(Filter::Op(
                                    Field::new("isTCP"),
                                    FilterOp::Ordering(OrderingOp::Equal, RhsValue::Bool(true)),
                                )),
                            ),
                        ],
                    ),
                    Filter::Op(
                        Field::new("port"),
                        FilterOp::Ordering(OrderingOp::GreaterThanEqual, RhsValue::Unsigned(1024)),
                    ),
                ]
            ))
        );
    }
}
