use bytes::Bytes;
use cidr::Cidr;
use field::Field;
use lex::{expect, span, Lex, LexError, LexErrorKind, LexResult};
use op::{BytesOp, CombiningOp, ComparisonOp, OrderingMask, UnaryOp, UnsignedOp};
use regex::bytes::Regex;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Error;
use types::{GetType, LhsValue, RhsValue, RhsValues, Type};

use std::borrow::Borrow;
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::FromIterator;

pub struct Context<K, T> {
    fields: HashMap<K, T>,
}

impl<K: Hash + Eq, T> FromIterator<(K, T)> for Context<K, T> {
    fn from_iter<I: IntoIterator<Item = (K, T)>>(iter: I) -> Self {
        Context {
            fields: HashMap::from_iter(iter),
        }
    }
}

fn combining_op(input: &str) -> (Option<CombiningOp>, &str) {
    match CombiningOp::lex(input) {
        Ok((op, input)) => (Some(op), input.trim_left()),
        Err(_) => (None, input),
    }
}

impl<K: Borrow<str> + Hash + Eq, T: GetType> Context<K, T> {
    fn simple_filter<'i>(&'i self, input: &'i str) -> LexResult<'i, Filter<'i>> {
        if let Ok(input) = expect(input, "(") {
            let input = input.trim_left();
            let (res, input) = self.combined_filter(input)?;
            let input = input.trim_left();
            let input = expect(input, ")")?;
            return Ok((res, input.trim_left()));
        }

        let initial_input = input;

        let (lhs, input) = Field::lex(input)?;

        let lhs_type = self.fields
            .get(lhs.path)
            .ok_or_else(|| (LexErrorKind::UnknownField, lhs.path))?
            .get_type();

        let input = input.trim_left();

        if let Ok(input) = expect(input, "in") {
            let input = input.trim_left();
            let (values, input) = RhsValues::lex(input, lhs_type)?;
            return Ok((Filter::OneOf(lhs, values), input));
        }

        let (op, input) = ComparisonOp::lex(input)?;

        let input = input.trim_left();

        let (filter, input) = match (lhs_type, op) {
            (_, ComparisonOp::Any(mask)) => {
                let (rhs, input) = RhsValue::lex(input, lhs_type)?;
                (Filter::Ordering(lhs, mask, rhs), input)
            }
            (Type::Unsigned, ComparisonOp::Unsigned(op)) => {
                let (rhs, input) = u64::lex(input)?;
                (Filter::Unsigned(lhs, op, rhs), input)
            }
            (Type::Bytes, ComparisonOp::Bytes(op)) => match op {
                BytesOp::Contains => {
                    let (rhs, input) = Bytes::lex(input)?;
                    (Filter::Contains(lhs, rhs), input)
                }
                BytesOp::Matches => {
                    let (rhs, input) = Regex::lex(input)?;
                    (Filter::Matches(lhs, rhs), input)
                }
            },
            (ty, op) => {
                return Err((
                    LexErrorKind::UnsupportedOp(ty, op),
                    span(initial_input, input),
                ))
            }
        };

        Ok((filter, input.trim_left()))
    }

    fn filter_prec<'i>(
        &'i self,
        mut lhs: Filter<'i>,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Filter<'i>> {
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

    fn combined_filter<'i>(&'i self, input: &'i str) -> LexResult<'i, Filter<'i>> {
        let (lhs, input) = self.simple_filter(input)?;
        let lookahead = combining_op(input);
        self.filter_prec(lhs, None, lookahead)
    }

    pub fn parse<'i>(&'i self, input: &'i str) -> Result<Filter<'i>, LexError<'i>> {
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

macro_rules! get_typed_field {
    ($context:ident, $field:ident, Type :: $ty:ident) => {
        match $context.get_field($field) {
            &LhsValue::$ty(ref value) => value,
            other => panic_type!($field, other.get_type(), Type::$ty)
        }
    };
}

impl<K: Borrow<str> + Hash + Eq> Context<K, LhsValue> {
    fn get_field(&self, field: Field) -> &LhsValue {
        self.fields
            .get(field.path)
            .unwrap_or_else(|| panic!("Could not find previously registered field {:?}", field))
    }

    pub fn execute<'i>(&'i self, filter: &'i Filter<'i>) -> bool {
        match *filter {
            Filter::Ordering(field, mask, ref rhs) => {
                let lhs = self.get_field(field);
                mask.contains(
                    lhs.partial_cmp(rhs)
                        .unwrap_or_else(|| {
                            panic_type!(field, lhs.get_type(), rhs.get_type());
                        })
                        .into(),
                )
            }
            Filter::Unsigned(field, UnsignedOp::BitwiseAnd, rhs) => {
                (get_typed_field!(self, field, Type::Unsigned) & rhs) == rhs
            }
            Filter::Contains(field, ref rhs) => {
                get_typed_field!(self, field, Type::Bytes).contains(rhs)
            }
            Filter::Matches(field, ref regex) => {
                regex.is_match(get_typed_field!(self, field, Type::Bytes))
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
            Filter::OneOf(field, ref values) => match *values {
                RhsValues::Ip(ref networks) => networks
                    .iter()
                    .any(|network| network.contains(get_typed_field!(self, field, Type::Ip))),

                RhsValues::Bytes(ref values) => values
                    .iter()
                    .any(|value| get_typed_field!(self, field, Type::Bytes) == value),

                RhsValues::Unsigned(ref values) => values
                    .iter()
                    .any(|value| get_typed_field!(self, field, Type::Unsigned) == value),
            },
        }
    }
}

fn serialize_regex<S: Serializer>(regex: &Regex, ser: S) -> Result<S::Ok, S::Error> {
    regex.as_str().serialize(ser)
}

fn deserialize_regex<'de, D: Deserializer<'de>>(de: D) -> Result<Regex, D::Error> {
    let src = Deserialize::deserialize(de)?;
    Regex::new(src).map_err(D::Error::custom)
}

#[derive(Debug, Serialize, Deserialize)]
pub enum Filter<'i> {
    Ordering(#[serde(borrow)] Field<'i>, OrderingMask, RhsValue),
    Unsigned(#[serde(borrow)] Field<'i>, UnsignedOp, u64),
    Contains(#[serde(borrow)] Field<'i>, Bytes),
    Matches(
        #[serde(borrow)] Field<'i>,
        #[serde(serialize_with = "serialize_regex", deserialize_with = "deserialize_regex")] Regex,
    ),
    OneOf(#[serde(borrow)] Field<'i>, RhsValues),
    Combine(CombiningOp, Vec<Filter<'i>>),
    Unary(UnaryOp, Box<Filter<'i>>),
}

impl<'i> Filter<'i> {
    pub fn uses(&self, field: Field<'i>) -> bool {
        match *self {
            Filter::Ordering(uses, ..)
            | Filter::Unsigned(uses, ..)
            | Filter::Contains(uses, ..)
            | Filter::Matches(uses, ..)
            | Filter::OneOf(uses, ..) => field == uses,

            Filter::Combine(_, ref filters) => filters.iter().any(|filter| filter.uses(field)),

            Filter::Unary(_, ref filter) => filter.uses(field),
        }
    }
}
