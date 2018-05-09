use lex::{expect, take_while, Lex, LexErrorKind, LexResult};

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

#[test]
fn test() {
    assert_ok!(u64::lex("0"), 0u64, "");
    assert_ok!(u64::lex("0-"), 0u64, "-");
    assert_ok!(u64::lex("0x1f5+"), 501u64, "+");
    assert_ok!(u64::lex("0123;"), 83u64, ";");
    assert_ok!(u64::lex("78!"), 78u64, "!");
    assert_ok!(u64::lex("0xefg"), 239u64, "g");
}
