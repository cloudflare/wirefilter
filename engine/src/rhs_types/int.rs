use lex::{expect, span, take_while, Lex, LexErrorKind, LexResult};
use std::ops::RangeInclusive;
use strict_partial_ord::StrictPartialOrd;

fn number(input: &str, radix: u32) -> LexResult<i32> {
    let (digits, input) = take_while(input, "digit", |c| c.is_digit(radix))?;
    match i32::from_str_radix(digits, radix) {
        Ok(res) => Ok((res, input)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, digits)),
    }
}

impl<'i> Lex<'i> for i32 {
    fn lex(input: &str) -> LexResult<Self> {
        if let Ok(input) = expect(input, "0") {
            match input.chars().next() {
                Some(c) if c.is_digit(8) => number(input, 8),
                Some('x') => number(&input[1..], 16),
                _ => Ok((0, input)),
            }
        } else {
            number(input, 10)
        }
    }
}

impl<'i> Lex<'i> for RangeInclusive<i32> {
    fn lex(input: &str) -> LexResult<Self> {
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
    assert_ok!(i32::lex("0"), 0i32, "");
    assert_ok!(i32::lex("0-"), 0i32, "-");
    assert_ok!(i32::lex("0x1f5+"), 501i32, "+");
    assert_ok!(i32::lex("0123;"), 83i32, ";");
    assert_ok!(i32::lex("78!"), 78i32, "!");
    assert_ok!(i32::lex("0xefg"), 239i32, "g");
    assert_ok!(RangeInclusive::lex("78!"), 78i32..=78i32, "!");
    assert_ok!(RangeInclusive::lex("0..10"), 0i32..=10i32);
    assert_ok!(RangeInclusive::lex("0123..0xefg"), 83i32..=239i32, "g");
    assert_err!(
        <RangeInclusive<i32>>::lex("10..0"),
        LexErrorKind::IncompatibleRangeBounds,
        "10..0"
    );
}
