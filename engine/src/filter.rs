use bytes::Bytes;
use field::Field;
use fnv::FnvBuildHasher;
use lex::{expect, span, Lex, LexError, LexErrorKind, LexResult};
use op::{BytesOp, CombiningOp, ComparisonOp, OrderingOp, UnaryOp, UnsignedOp};
use ordermap::OrderMap;
use re::Regex;
use types::{GetType, LhsValue, RhsValue, RhsValues, Type};

use std::borrow::Borrow;
use std::hash::Hash;
use std::iter::FromIterator;

pub struct Context<K, T> {
    fields: OrderMap<K, T, FnvBuildHasher>,
}

impl<K: Hash + Eq, T> Context<K, T> {
    pub fn insert(&mut self, key: K, value: T) {
        self.fields.insert(key, value);
    }
}

impl<K: Hash + Eq, T> Default for Context<K, T> {
    fn default() -> Self {
        Context {
            fields: OrderMap::default(),
        }
    }
}

impl<K: Hash + Eq, T> FromIterator<(K, T)> for Context<K, T> {
    fn from_iter<I: IntoIterator<Item = (K, T)>>(iter: I) -> Self {
        Context {
            fields: OrderMap::from_iter(iter),
        }
    }
}

fn combining_op(input: &str) -> (Option<CombiningOp>, &str) {
    match CombiningOp::lex(input) {
        Ok((op, input)) => (Some(op), input.trim_left()),
        Err(_) => (None, input),
    }
}

impl<'c, K: Borrow<str> + Hash + Eq, T: GetType> Context<K, T> {
    fn simple_filter<'i>(&'c self, input: &'i str) -> LexResult<'i, Filter<'c>> {
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

        let (_, lhs, lhs_type) = self.fields
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
                (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                    BytesOp::Contains => {
                        let (rhs, input) = Bytes::lex(input)?;
                        (FilterOp::Contains(rhs), input)
                    }
                    BytesOp::Matches => {
                        let (rhs, input) = Regex::lex(input)?;
                        (FilterOp::Matches(rhs), input)
                    }
                },
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
        &'c self,
        mut lhs: Filter<'c>,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Filter<'c>> {
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

    fn combined_filter<'i>(&'c self, input: &'i str) -> LexResult<'i, Filter<'c>> {
        let (lhs, input) = self.simple_filter(input)?;
        let lookahead = combining_op(input);
        self.filter_prec(lhs, None, lookahead)
    }

    pub fn parse<'i>(&'c self, input: &'i str) -> Result<Filter<'c>, LexError<'i>> {
        let (res, input) = self.combined_filter(input)?;
        if input.is_empty() {
            Ok(res)
        } else {
            Err((LexErrorKind::EOF, input))
        }
    }
}

macro_rules! panic_type {
    ($field:expr, $actual:expr, $expected:expr) => {
        panic!(
            "Field {:?} was previously registered with type {:?} but now contains {:?}",
            $field,
            $expected.get_type(),
            $actual.get_type()
        );
    };
}

macro_rules! cast_field {
    ($field:ident, $lhs:ident, $ty:ident) => {
        match $lhs {
            &LhsValue::$ty(ref value) => value,
            other => panic_type!($field, other, Type::$ty)
        }
    };
}

impl<'a, K: Borrow<str> + Hash + Eq, V: Borrow<LhsValue<'a>>> Context<K, V> {
    fn get_field(&self, field: Field) -> &LhsValue<'a> {
        self.fields
            .get(field.path())
            .unwrap_or_else(|| panic!("Could not find previously registered field {:?}", field))
            .borrow()
    }

    pub fn execute(&self, filter: &Filter) -> bool {
        match *filter {
            Filter::Op(field, ref op) => {
                let lhs = self.get_field(field);

                match *op {
                    FilterOp::Ordering(op, ref rhs) => lhs.try_cmp(op, rhs).unwrap_or_else(|()| {
                        panic_type!(field, lhs, rhs);
                    }),
                    FilterOp::Unsigned(UnsignedOp::BitwiseAnd, rhs) => {
                        cast_field!(field, lhs, Unsigned) & rhs != 0
                    }
                    FilterOp::Contains(ref rhs) => cast_field!(field, lhs, Bytes).contains(rhs),
                    FilterOp::Matches(ref regex) => regex.is_match(cast_field!(field, lhs, Bytes)),
                    FilterOp::OneOf(ref values) => values
                        .try_contains(lhs)
                        .unwrap_or_else(|()| panic_type!(field, lhs, values)),
                }
            }
            Filter::Combine(op, ref filters) => {
                let mut results = filters.iter().map(|filter| self.execute(filter));
                match op {
                    CombiningOp::And => results.all(|res| res),
                    CombiningOp::Or => results.any(|res| res),
                    CombiningOp::Xor => results.fold(false, |acc, res| acc ^ res),
                }
            }
            Filter::Unary(UnaryOp::Not, ref filter) => !self.execute(filter),
        }
    }
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum FilterOp<'a> {
    Ordering(OrderingOp, #[serde(borrow)] RhsValue<'a>),
    Unsigned(UnsignedOp, u64),
    Contains(#[serde(borrow)] Bytes<'a>),
    Matches(Regex),
    OneOf(#[serde(borrow)] RhsValues<'a>),
}

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Filter<'a> {
    Op(#[serde(borrow)] Field<'a>, #[serde(borrow)] FilterOp<'a>),
    Combine(CombiningOp, Vec<Filter<'a>>),
    Unary(UnaryOp, Box<Filter<'a>>),
}

impl<'a> Filter<'a> {
    pub fn uses(&self, field: Field) -> bool {
        match *self {
            Filter::Op(lhs, ..) => field == lhs,
            Filter::Combine(_, ref filters) => filters.iter().any(|filter| filter.uses(field)),
            Filter::Unary(_, ref filter) => filter.uses(field),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use types::LhsValue;

    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

    #[test]
    fn parse() {
        use cidr::{Cidr, IpCidr, Ipv4Cidr, Ipv6Cidr};
        use types::{RhsValue, Type};

        let context: Context<_, _> = [
            ("http.host", Type::Bytes),
            ("port", Type::Unsigned),
            ("ip.src", Type::Ip),
            ("isTCP", Type::Bool),
        ].iter()
            .cloned()
            .collect();

        assert_eq!(
            context.parse("http.host contains \"t\""),
            Ok(Filter::Op(
                Field::new("http.host"),
                FilterOp::Contains(Bytes::from("t"))
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

    fn assert_filter(context: &Context<&str, LhsValue>, filter: &str, expect: bool) {
        let filter = context.parse(filter).unwrap();
        assert_eq!(context.execute(&filter), expect);
    }

    #[test]
    fn compare_ip() {
        let mut context = Context::default();
        context.insert("ip", LhsValue::Ip(IpAddr::V6(Ipv6Addr::from(2))));

        assert_filter(&context, "ip > ::1", true);
        assert_filter(&context, "ip <= ::3", true);
        assert_filter(&context, "ip > ::2", false);
        assert_filter(&context, "ip < 127.0.0.3", false);
        assert_filter(&context, "ip >= 127.0.0.1 and ip < 127.0.0.255", false);
        assert_filter(&context, "ip == 127.0.0.0/8", false);
        assert_filter(&context, "ip != 127.0.0.0/8", true);
    }

    #[test]
    fn check_bool() {
        let mut context = Context::default();
        context.insert("true", LhsValue::Bool(true));
        context.insert("false", LhsValue::Bool(false));

        assert_filter(&context, "true", true);
        assert_filter(&context, "not true", false);
        assert_filter(&context, "false", false);
        assert_filter(&context, "!false", true);
    }
}
