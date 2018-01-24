use bytes::Bytes;
use cidr::Cidr;
use field::Field;
use fnv::FnvBuildHasher;
use lex::{expect, span, Lex, LexError, LexErrorKind, LexResult};
use op::{BytesOp, CombiningOp, ComparisonOp, OrderingOp, UnaryOp, UnsignedOp};
use ordermap::OrderMap;
use regex::bytes::Regex;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Error;
use types::{GetType, LhsValue, RhsValue, RhsValues, Type};

use std::borrow::{Borrow, Cow};
use std::hash::Hash;
use std::iter::FromIterator;

pub struct Context<K, T> {
    fields: OrderMap<K, T, FnvBuildHasher>,
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
            $expected,
            $actual
        );
    };
}

macro_rules! cast_field {
    ($field:ident, $lhs:ident, $ty:ident) => {
        match $lhs {
            &LhsValue::$ty(ref value) => value,
            other => panic_type!($field, other.get_type(), Type::$ty)
        }
    };
}

impl<K: Borrow<str> + Hash + Eq> Context<K, LhsValue> {
    fn get_field(&self, field: Field) -> &LhsValue {
        self.fields
            .get(field.path())
            .unwrap_or_else(|| panic!("Could not find previously registered field {:?}", field))
    }

    pub fn execute(&self, filter: &Filter) -> bool {
        match *filter {
            Filter::Op(field, ref op) => {
                let lhs = self.get_field(field);

                match *op {
                    FilterOp::Ordering(mask, ref rhs) => {
                        mask.contains(lhs.partial_cmp(rhs).unwrap_or_else(|| {
                            panic_type!(field, lhs.get_type(), rhs.get_type());
                        }))
                    }
                    FilterOp::Unsigned(UnsignedOp::BitwiseAnd, rhs) => {
                        cast_field!(field, lhs, Unsigned) & rhs != 0
                    }
                    FilterOp::Contains(ref rhs) => cast_field!(field, lhs, Bytes).contains(rhs),
                    FilterOp::Matches(ref regex) => regex.is_match(cast_field!(field, lhs, Bytes)),
                    FilterOp::OneOf(ref values) => match *values {
                        RhsValues::Ip(ref networks) => {
                            let lhs = cast_field!(field, lhs, Ip);
                            networks.iter().any(|network| network.contains(lhs))
                        }
                        RhsValues::Bytes(ref values) => {
                            let lhs = cast_field!(field, lhs, Bytes);
                            values.iter().any(|value| lhs == value)
                        }
                        RhsValues::Unsigned(ref values) => {
                            let lhs = cast_field!(field, lhs, Unsigned);
                            values.iter().any(|value| lhs == value)
                        }
                    },
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

#[derive(Serialize, Deserialize)]
struct RegexRepr<'i>(#[serde(borrow)] Cow<'i, str>);

impl<'i> RegexRepr<'i> {
    fn serialize<S: Serializer>(regex: &Regex, ser: S) -> Result<S::Ok, S::Error> {
        Serialize::serialize(&RegexRepr(Cow::Borrowed(regex.as_str())), ser)
    }

    fn deserialize<'de, D: Deserializer<'de>>(de: D) -> Result<Regex, D::Error> {
        let src: RegexRepr = Deserialize::deserialize(de)?;
        Regex::new(&src.0).map_err(D::Error::custom)
    }
}

#[derive(Debug, Serialize, Deserialize)]
pub enum FilterOp {
    Ordering(OrderingOp, RhsValue),
    Unsigned(UnsignedOp, u64),
    Contains(Bytes),
    Matches(#[serde(with = "RegexRepr")] Regex),
    OneOf(RhsValues),
}

#[derive(Debug, Serialize, Deserialize)]
pub enum Filter<'a> {
    Op(#[serde(borrow)] Field<'a>, FilterOp),
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
