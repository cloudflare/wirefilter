use {ErrorKind, Lex, LexResult};
use std::fmt::{self, Debug, Formatter};
use std::ops::Deref;
use utils::{expect, hex_byte, oct_byte, take_while};

pub struct Bytes {
    is_str: bool,
    raw: Vec<u8>,
}

extern "C" {
    fn memmem(
        haystack: *const u8,
        haystack_len: usize,
        needle: *const u8,
        needle_len: usize,
    ) -> *const u8;
}

impl Bytes {
    pub fn is_str(&self) -> bool {
        self.is_str
    }

    pub fn contains(&self, rhs: &[u8]) -> bool {
        unsafe { !memmem(self.as_ptr(), self.len(), rhs.as_ptr(), rhs.len()).is_null() }
    }
}

impl From<String> for Bytes {
    fn from(src: String) -> Self {
        Bytes {
            is_str: true,
            raw: src.into_bytes(),
        }
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(raw: Vec<u8>) -> Self {
        Bytes { is_str: false, raw }
    }
}

impl Debug for Bytes {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.is_str {
            unsafe {
                ::std::str::from_utf8_unchecked(&self.raw)
            }.fmt(f)
        } else {
            for (i, b) in self.raw.iter().cloned().enumerate() {
                if i != 0 {
                    write!(f, ":")?;
                }
                write!(f, "{:02X}", b)?;
            }
            Ok(())
        }
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.raw
    }
}

impl<'a> Lex<'a> for Bytes {
    fn lex(input: &'a str) -> LexResult<'a, Self> {
        if let Ok(input) = expect(input, "\"") {
            let mut res = String::new();
            let mut iter = input.chars();
            loop {
                match iter.next().ok_or_else(|| (ErrorKind::EndingQuote, input))? {
                    '\\' => {
                        let input = iter.as_str();
                        let (b, input) = (if let Ok(input) = expect(input, "\"") {
                            Ok((b'"', input))
                        } else if let Ok(input) = expect(input, "\\") {
                            Ok((b'\\', input))
                        } else if let Ok(input) = expect(input, "x") {
                            hex_byte(input)
                        } else {
                            oct_byte(input).map_err(|_| (ErrorKind::CharacterEscape, input))
                        })?;
                        res.push(b as char);
                        iter = input.chars();
                    }
                    '"' => return Ok((res.into(), iter.as_str())),
                    c => res.push(c),
                };
            }
        } else {
            let (chunk, rest) =
                take_while(input, "non-whitespace character", |c| !c.is_whitespace())?;
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
                .map(|res| (res.into(), rest))
        }
    }
}
