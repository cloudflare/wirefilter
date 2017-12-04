use tokenizer::{ErrorKind, Lex, LexResult};
use tokenizer::utils::{expect, hex_byte, oct_byte};

impl<'a> Lex<'a> for String {
    fn lex(input: &'a str) -> LexResult<'a, Self> {
        let input = expect(input, "\"")?;
        let mut res = String::new();
        let mut iter = input.chars();
        loop {
            match iter.next().ok_or_else(|| (ErrorKind::EndingQuote, input))? {
                '\\' => {
                    let input = iter.as_str();
                    let (b, input) = (if let Ok(input) = expect(input, "\"") {
                        Ok((b'"', input))
                    } else if let Ok(input) = expect(input, "x") {
                        hex_byte(input)
                    } else {
                        oct_byte(input).map_err(|_| (ErrorKind::CharacterEscape, input))
                    })?;
                    res.push(b as char);
                    iter = input.chars();
                }
                '"' => return Ok((res, iter.as_str())),
                c => res.push(c),
            };
        }
    }
}
