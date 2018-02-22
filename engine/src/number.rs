use lex::{expect, take_while, Lex, LexErrorKind, LexResult};

use std::str::FromStr;

fn number(input: &str, radix: u32) -> LexResult<u64> {
    let (digits, input) = take_while(input, "digit", |c| c.is_digit(radix))?;
    match u64::from_str_radix(digits, radix) {
        Ok(res) => Ok((res, input)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, digits)),
    }
}

impl<'i> Lex<'i> for u64 {
    fn lex(input: &str) -> LexResult<u64> {
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

fn index(input: &str) -> LexResult<isize> {
    let (neg, input) = match expect(input, "-") {
        Ok(input) => (true, input),
        Err(_) => (false, input),
    };
    let (digits, input) = take_while(input, "digit", |c| c.is_digit(10))?;
    match isize::from_str(digits) {
        Ok(mut res) => {
            if neg {
                res = -res;
            }
            Ok((res, input))
        }
        Err(err) => Err((LexErrorKind::ParseInt { err, radix: 10 }, digits)),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub start: isize,
    pub end: isize,
}

impl<'i> Lex<'i> for Range {
    fn lex(input: &str) -> LexResult<Self> {
        let (start, input) = if input.starts_with(':') {
            (0, input)
        } else {
            index(input)?
        };
        let (end, input) = if let Ok(input) = expect(input, ":") {
            match index(input) {
                Ok((len, input)) => (start + len - 1, input),
                Err(_) => (-1, input),
            }
        } else if let Ok(input) = expect(input, "-") {
            let (end, input) = index(input)?;
            (end, input)
        } else {
            (start, input)
        };
        Ok((Range { start, end }, input))
    }
}

pub type Ranges = Vec<Range>;

impl<'i> Lex<'i> for Ranges {
    fn lex(input: &str) -> LexResult<Self> {
        let mut input = expect(input, "[")?.trim_left();
        let mut res = Vec::new();
        loop {
            let (item, rest) = Range::lex(input)?;
            res.push(item);
            let rest = rest.trim_left();
            if let Ok(rest) = expect(rest, ",") {
                input = rest.trim_left();
            } else {
                return Ok((res, expect(rest, "]")?));
            }
        }
    }
}

#[test]
fn test_number() {
    assert_ok!(u64::lex("0"), 0u64, "");
    assert_ok!(u64::lex("0-"), 0u64, "-");
    assert_ok!(u64::lex("0x1f5+"), 501u64, "+");
    assert_ok!(u64::lex("0123;"), 83u64, ";");
    assert_ok!(u64::lex("78!"), 78u64, "!");
    assert_ok!(u64::lex("0xefg"), 239u64, "g");
}

#[test]
fn test_ranges() {
    assert_ok!(Ranges::lex("[1];"), vec![Range { start: 1, end: 1 }], ";");
    assert_ok!(Ranges::lex("[0:3];"), vec![Range { start: 0, end: 2 }], ";");
    assert_ok!(
        Ranges::lex("[-3];"),
        vec![Range { start: -3, end: -3 }],
        ";"
    );
    assert_ok!(Ranges::lex("[:]"), vec![Range { start: 0, end: -1 }], "");
    assert_ok!(
        Ranges::lex("[1,:2,3-4,7:,9:10];"),
        vec![
            Range { start: 1, end: 1 },
            Range { start: 0, end: 1 },
            Range { start: 3, end: 4 },
            Range { start: 7, end: -1 },
            Range { start: 9, end: 18 },
        ],
        ";"
    );
    assert_err!(
        Ranges::lex("[1-]"),
        LexErrorKind::ExpectedName("digit"),
        "]"
    );
    assert_err!(
        Ranges::lex("[--9]"),
        LexErrorKind::ExpectedName("digit"),
        "-9]"
    );
    assert_err!(Ranges::lex("[-]"), LexErrorKind::ExpectedName("digit"), "]");
    assert_err!(Ranges::lex("[]"), LexErrorKind::ExpectedName("digit"), "]");
}
