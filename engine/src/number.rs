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
                _ => Ok((0, input))
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
    pub end: Option<isize>,
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
                Ok((len, input)) => (Some(start + len), input),
                Err(_) => (None, input),
            }
        } else if let Ok(input) = expect(input, "-") {
            let (end, input) = index(input)?;
            (Some(start + end - 1), input)
        } else {
            (None, input)
        };
        Ok((Range { start, end }, input))
    }
}

impl<'i> Lex<'i> for Vec<Range> {
    fn lex(input: &str) -> LexResult<Self> {
        let mut input = expect(input, "[")?;
        let mut res = Vec::new();
        loop {
            let (item, rest) = Range::lex(input)?;
            res.push(item);
            if let Ok(rest) = expect(rest.trim_left(), ",") {
                input = rest.trim_left();
            } else {
                return Ok((res, input));
            }
        }
    }
}

#[test]
fn test() {
    assert_ok!(u64::lex("0"), 0u64, "");
    assert_ok!(u64::lex("0-"), 0u64, "-");
    assert_ok!(u64::lex("0x1f5+"), 501u64, "+");
    assert_ok!(u64::lex("0123;"), 83u64, ";");
    assert_ok!(u64::lex("78!"), 78u64, "!");
    assert_ok!(u64::lex("0xefg"), 239u64, "g");
}