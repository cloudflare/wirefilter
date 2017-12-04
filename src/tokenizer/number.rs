use tokenizer::{ErrorKind, Lex, LexResult};
use tokenizer::utils::{expect, take_while};

fn number(input: &str, radix: u32) -> LexResult<u64> {
    let (digits, input) = take_while(input, "digit", |c| c.is_digit(radix))?;
    match u64::from_str_radix(digits, radix) {
        Ok(res) => Ok((res, input)),
        Err(e) => Err((ErrorKind::ParseInt(e, radix), digits)),
    }
}

impl<'a> Lex<'a> for u64 {
    fn lex(input: &'a str) -> LexResult<'a, u64> {
        if let Ok(input) = expect(input, "0x") {
            number(input, 16)
        } else if let Ok(input) = expect(input, "0") {
            number(input, 8)
        } else {
            number(input, 10)
        }
    }
}
