use crate::{
    lex::{expect, span, take_while, Lex, LexErrorKind, LexResult},
    strict_partial_ord::StrictPartialOrd,
};
use serde::Serialize;
use std::ops::RangeInclusive;

fn lex_digits(input: &str) -> LexResult<'_, &str> {
    // Lex any supported digits (up to radix 16) for better error locations.
    take_while(input, "digit", |c| c.is_ascii_hexdigit())
}

fn parse_number<'i>((input, rest): (&'i str, &'i str), radix: u32) -> LexResult<'i, i64> {
    match i64::from_str_radix(input, radix) {
        Ok(res) => Ok((res, rest)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, input)),
    }
}

impl<'i> Lex<'i> for i64 {
    fn lex(input: &str) -> LexResult<'_, Self> {
        if let Ok(input) = expect(input, "0x") {
            parse_number(lex_digits(input)?, 16)
        } else if input.starts_with('0') {
            // not using `expect` because we want to include `0` too
            parse_number(lex_digits(input)?, 8)
        } else {
            let without_neg = match expect(input, "-") {
                Ok(input) => input,
                Err(_) => input,
            };

            let (_, rest) = lex_digits(without_neg)?;

            parse_number((span(input, rest), rest), 10)
        }
    }
}

/// A range of integers defined by start and end.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize)]
#[serde(transparent)]
pub struct IntRange(RangeInclusive<i64>);

impl From<i64> for IntRange {
    fn from(i: i64) -> Self {
        IntRange(i..=i)
    }
}

impl From<RangeInclusive<i64>> for IntRange {
    fn from(r: RangeInclusive<i64>) -> Self {
        IntRange(r)
    }
}

impl<'i> Lex<'i> for IntRange {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let initial_input = input;
        let (first, input) = i64::lex(input)?;
        let (last, input) = if let Ok(input) = expect(input, "..") {
            i64::lex(input)?
        } else {
            (first, input)
        };
        if last < first {
            return Err((
                LexErrorKind::IncompatibleRangeBounds,
                span(initial_input, input),
            ));
        }
        Ok(((first..=last).into(), input))
    }
}

impl From<IntRange> for RangeInclusive<i64> {
    fn from(range: IntRange) -> Self {
        range.0
    }
}

impl<'a> From<&'a IntRange> for RangeInclusive<i64> {
    fn from(range: &'a IntRange) -> Self {
        RangeInclusive::new(*range.0.start(), *range.0.end())
    }
}

impl StrictPartialOrd for i64 {}

#[test]
fn test() {
    use std::str::FromStr;

    assert_ok!(i64::lex("0"), 0i64, "");
    assert_ok!(i64::lex("0-"), 0i64, "-");
    assert_ok!(i64::lex("0x1f5+"), 501i64, "+");
    assert_ok!(i64::lex("0123;"), 83i64, ";");
    assert_ok!(i64::lex("78!"), 78i64, "!");
    assert_ok!(i64::lex("0xefg"), 239i64, "g");
    assert_ok!(i64::lex("-12-"), -12i64, "-");
    assert_err!(
        i64::lex("-9223372036854775809!"),
        LexErrorKind::ParseInt {
            err: i64::from_str("-9223372036854775809").unwrap_err(),
            radix: 10
        },
        "-9223372036854775809"
    );
    assert_err!(
        i64::lex("9223372036854775808!"),
        LexErrorKind::ParseInt {
            err: i64::from_str("9223372036854775808").unwrap_err(),
            radix: 10
        },
        "9223372036854775808"
    );
    assert_err!(
        i64::lex("10fex"),
        LexErrorKind::ParseInt {
            err: i64::from_str("10fe").unwrap_err(),
            radix: 10
        },
        "10fe"
    );
    assert_ok!(IntRange::lex("78!"), 78i64.into(), "!");
    assert_ok!(IntRange::lex("0..10"), (0i64..=10i64).into());
    assert_ok!(IntRange::lex("0123..0xefg"), (83i64..=239i64).into(), "g");
    assert_ok!(IntRange::lex("-20..-10"), (-20i64..=-10i64).into());
    assert_err!(
        IntRange::lex("10..0"),
        LexErrorKind::IncompatibleRangeBounds,
        "10..0"
    );
}
