use {ErrorKind, Lex, LexResult};
use std::fmt::{self, Debug, Formatter};
use std::ops::Deref;
use utils::{expect, hex_byte, oct_byte};

#[derive(PartialEq, Eq)]
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

    pub fn as_str(&self) -> Option<&str> {
        if self.is_str {
            Some(unsafe { ::std::str::from_utf8_unchecked(self) })
        } else {
            None
        }
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
        if let Some(s) = self.as_str() {
            s.fmt(f)
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

simple_enum!(ByteSeparator {
    ":" => Colon,
    "-" => Dash,
    "." => Dot,
});

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
            let (b, input) = hex_byte(input)?;
            let (_, mut input) = ByteSeparator::lex(input)?;
            let mut res = vec![b];
            loop {
                let (b, rest) = hex_byte(input)?;
                res.push(b);
                input = rest;
                if let Ok((_, rest)) = ByteSeparator::lex(input) {
                    input = rest;
                } else {
                    break;
                }
            }
            Ok((res.into(), input))
        }
    }
}

#[test]
fn test() {
    assert_ok!(
        Bytes::lex("01:2e:f3-77.12;"),
        Bytes::from(vec![0x01, 0x2E, 0xF3, 0x77, 0x12]),
        ";"
    );

    assert_ok!(
        Bytes::lex(r#""s\\t\"r\x0A\000t""#),
        Bytes::from("s\\t\"r\n\0t".to_owned())
    );

    assert_err!(
        Bytes::lex("01:4x;"),
        ErrorKind::ParseInt(u8::from_str_radix("4x", 16).unwrap_err(), 16),
        "4x"
    );

    assert_err!(
        Bytes::lex("01;"),
        ErrorKind::Enum("ByteSeparator", &[":", "-", "."]),
        ";"
    );

    assert_ok!(
        Bytes::lex("01:2f-34"),
        Bytes::from(vec![0x01, 0x2F, 0x34])
    );

    assert_err!(
        Bytes::lex("\"1"),
        ErrorKind::EndingQuote,
        "1"
    );

    assert_err!(
        Bytes::lex(r#""\n""#),
        ErrorKind::CharacterEscape,
        "n\""
    );
}
