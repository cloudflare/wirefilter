use {ErrorKind, Lex, LexResult};
use utils::take_while;

impl<'a> Lex<'a> for Vec<u8> {
    fn lex(input: &'a str) -> LexResult<'a, Self> {
        let (chunk, rest) = take_while(input, "non-whitespace character", |c| !c.is_whitespace())?;
        chunk
            .split(|c| c == ':' || c == '-' || c == '.')
            .map(|s| u8::from_str_radix(s, 16).map_err(|err| (ErrorKind::ParseInt(err, 16), s)))
            .collect::<Result<Vec<_>, _>>()
            .and_then(|res| {
                if res.len() < 2 {
                    Err((ErrorKind::CountMismatch("byte", res.len(), 2), input))
                } else {
                    Ok(res)
                }
            })
            .map(|res| (res, rest))
    }
}
