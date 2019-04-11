use crate::{
    lex::{expect, span, take_while, Lex, LexErrorKind, LexResult},
    strict_partial_ord::StrictPartialOrd,
};
use std::ops::RangeInclusive;

fn lex_digits(input: &str) -> LexResult<'_, &str> {
    // Lex any supported digits (up to radix 16) for better error locations.
    take_while(input, "digit", |c| c.is_digit(16))
}

fn parse_number<'i>((input, rest): (&'i str, &'i str), radix: u32) -> LexResult<'_, i32> {
    match i32::from_str_radix(input, radix) {
        Ok(res) => Ok((res, rest)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, input)),
    }
}

impl<'i> Lex<'i> for i32 {
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

impl<'i> Lex<'i> for RangeInclusive<i32> {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let initial_input = input;
        let (first, input) = i32::lex(input)?;
        let (last, input) = if let Ok(input) = expect(input, "..") {
            i32::lex(input)?
        } else {
            (first, input)
        };
        if last < first {
            return Err((
                LexErrorKind::IncompatibleRangeBounds,
                span(initial_input, input),
            ));
        }
        Ok((first..=last, input))
    }
}

impl StrictPartialOrd for i32 {}

#[test]
fn test() {
    use std::str::FromStr;

    assert_ok!(i32::lex("0"), 0i32, "");
    assert_ok!(i32::lex("0-"), 0i32, "-");
    assert_ok!(i32::lex("0x1f5+"), 501i32, "+");
    assert_ok!(i32::lex("0123;"), 83i32, ";");
    assert_ok!(i32::lex("78!"), 78i32, "!");
    assert_ok!(i32::lex("0xefg"), 239i32, "g");
    assert_ok!(i32::lex("-12-"), -12i32, "-");
    assert_err!(
        i32::lex("-2147483649!"),
        LexErrorKind::ParseInt {
            err: i32::from_str("-2147483649").unwrap_err(),
            radix: 10
        },
        "-2147483649"
    );
    assert_err!(
        i32::lex("2147483648!"),
        LexErrorKind::ParseInt {
            err: i32::from_str("2147483648").unwrap_err(),
            radix: 10
        },
        "2147483648"
    );
    assert_err!(
        i32::lex("10fex"),
        LexErrorKind::ParseInt {
            err: i32::from_str("10fe").unwrap_err(),
            radix: 10
        },
        "10fe"
    );
    assert_ok!(RangeInclusive::lex("78!"), 78i32..=78i32, "!");
    assert_ok!(RangeInclusive::lex("0..10"), 0i32..=10i32);
    assert_ok!(RangeInclusive::lex("0123..0xefg"), 83i32..=239i32, "g");
    assert_ok!(RangeInclusive::lex("-20..-10"), -20i32..=-10i32);
    assert_err!(
        <RangeInclusive<i32>>::lex("10..0"),
        LexErrorKind::IncompatibleRangeBounds,
        "10..0"
    );
}
