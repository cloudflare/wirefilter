use crate::{
    lex::{expect, span, take_while, Lex, LexError, LexErrorKind, LexResult},
    strict_partial_ord::StrictPartialOrd,
};
use ordered_float::OrderedFloat;
use serde::Serialize;
use std::{fmt, ops::RangeInclusive, str::FromStr};

#[derive(Debug, Clone)]
struct ParseFloatError;

impl fmt::Display for ParseFloatError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid float")
    }
}

fn lex_floats(input: &str) -> LexResult<'_, &str> {
    take_while(input, "float", |c| match c {
        '0'..='9' | '.' => true,
        _ => false,
    })
}

fn parse_float<'i>(input: &'i str) -> Result<OrderedFloat<f64>, LexError<'_>> {
    match f64::from_str(input) {
        Ok(res) => Ok(OrderedFloat(res)),
        Err(err) => Err((LexErrorKind::ParseFloat { err }, input)),
    }
}

impl<'i> Lex<'i> for OrderedFloat<f64> {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let without_neg = match expect(input, "-") {
            Ok(input) => input,
            Err(_) => input,
        };

        let (_, rest) = lex_floats(without_neg)?;

        Ok((parse_float(span(input, rest))?, rest))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(transparent)]
pub struct FloatRange(RangeInclusive<OrderedFloat<f64>>);

impl From<OrderedFloat<f64>> for FloatRange {
    fn from(i: OrderedFloat<f64>) -> Self {
        FloatRange(i..=i)
    }
}

impl From<RangeInclusive<OrderedFloat<f64>>> for FloatRange {
    fn from(r: RangeInclusive<OrderedFloat<f64>>) -> Self {
        FloatRange(r)
    }
}

impl From<RangeInclusive<f64>> for FloatRange {
    fn from(r: RangeInclusive<f64>) -> Self {
        let (y, z) = r.into_inner();
        FloatRange(OrderedFloat(y)..=OrderedFloat(z))
    }
}

impl<'i> Lex<'i> for FloatRange {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let (chunk, rest) = lex_floats(input)?;

        let (first, last) = if let Some(split_pos) = chunk.find("..") {
            let first = parse_float(&chunk[..split_pos])?;
            let last = parse_float(&chunk[split_pos + "..".len()..])?;
            (first, last)
        } else {
            let initial = parse_float(chunk)?;
            (initial, initial)
        };
        if last < first {
            return Err((LexErrorKind::IncompatibleRangeBounds, input));
        }

        Ok((FloatRange(first..=last), rest))
    }
}

impl From<FloatRange> for RangeInclusive<OrderedFloat<f64>> {
    fn from(range: FloatRange) -> Self {
        range.0
    }
}

impl StrictPartialOrd for OrderedFloat<f64> {}

#[test]
fn test() {
    assert_ok!(OrderedFloat::lex("0.0"), OrderedFloat(0.0), "");
    assert_ok!(OrderedFloat::lex("1.5-"), OrderedFloat(1.5), "-");
    assert_ok!(
        FloatRange::lex("0.1..10.3"),
        (OrderedFloat(0.1)..=OrderedFloat(10.3)).into()
    );
    assert_err!(
        FloatRange::lex("10.3..0.1"),
        LexErrorKind::IncompatibleRangeBounds,
        "10.3..0.1"
    );
}
