use lex::{expect, hex_byte, oct_byte, span, Lex, LexErrorKind, LexResult};
use regex::bytes::{Regex, RegexBuilder};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::{self, Visitor};

use std::fmt::{self, Debug, Formatter};
use std::ops::Deref;
use std::str;

#[derive(PartialEq, Eq)]
pub enum Bytes {
    Str(Box<str>),
    Raw(Box<[u8]>),
}

impl Serialize for Bytes {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        match *self {
            Bytes::Str(ref s) => s.serialize(ser),
            Bytes::Raw(ref b) => b.serialize(ser),
        }
    }
}

impl<'de> Deserialize<'de> for Bytes {
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        struct BytesVisitor;

        impl<'de> Visitor<'de> for BytesVisitor {
            type Value = Bytes;

            fn expecting(&self, f: &mut Formatter) -> fmt::Result {
                f.write_str("a byte buffer or a string")
            }

            fn visit_bytes<E: de::Error>(self, v: &[u8]) -> Result<Bytes, E> {
                self.visit_byte_buf(v.into())
            }

            fn visit_byte_buf<E: de::Error>(self, v: Vec<u8>) -> Result<Bytes, E> {
                Ok(Bytes::from(v))
            }

            fn visit_str<E: de::Error>(self, v: &str) -> Result<Bytes, E> {
                self.visit_string(v.into())
            }

            fn visit_string<E: de::Error>(self, v: String) -> Result<Bytes, E> {
                Ok(Bytes::from(v))
            }
        }

        de.deserialize_byte_buf(BytesVisitor)
    }
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
    pub fn contains(&self, rhs: &[u8]) -> bool {
        unsafe { !memmem(self.as_ptr(), self.len(), rhs.as_ptr(), rhs.len()).is_null() }
    }
}

impl From<Box<str>> for Bytes {
    fn from(src: Box<str>) -> Self {
        Bytes::Str(src)
    }
}

impl From<String> for Bytes {
    fn from(src: String) -> Self {
        Self::from(src.into_boxed_str())
    }
}

impl From<Box<[u8]>> for Bytes {
    fn from(raw: Box<[u8]>) -> Self {
        Bytes::Raw(raw)
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(raw: Vec<u8>) -> Self {
        Self::from(raw.into_boxed_slice())
    }
}

impl Debug for Bytes {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Bytes::Str(ref s) => s.fmt(f),
            Bytes::Raw(ref b) => {
                for (i, b) in b.iter().cloned().enumerate() {
                    if i != 0 {
                        write!(f, ":")?;
                    }
                    write!(f, "{:02X}", b)?;
                }
                Ok(())
            }
        }
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        match *self {
            Bytes::Str(ref s) => s.as_bytes(),
            Bytes::Raw(ref b) => b,
        }
    }
}

lex_enum!(ByteSeparator {
    ":" => Colon,
    "-" => Dash,
    "." => Dot,
});

impl<'i> Lex<'i> for Regex {
    fn lex(input: &str) -> LexResult<Self> {
        let input = expect(input, "\"")?;
        let (regex_str, input) = {
            let mut iter = input.chars();
            loop {
                let before_char = iter.as_str();
                match iter.next()
                    .ok_or_else(|| (LexErrorKind::MissingEndingQuote, input))?
                {
                    '\\' => {
                        iter.next();
                    }
                    '"' => {
                        break (span(input, before_char), iter.as_str());
                    }
                    _ => {}
                };
            }
        };
        match RegexBuilder::new(regex_str).unicode(false).build() {
            Ok(regex) => Ok((regex, input)),
            Err(err) => Err((LexErrorKind::ParseRegex(err), regex_str)),
        }
    }
}

impl<'i> Lex<'i> for Bytes {
    fn lex(mut input: &str) -> LexResult<Self> {
        if let Ok(input) = expect(input, "\"") {
            let mut res = String::new();
            let mut iter = input.chars();
            loop {
                match iter.next()
                    .ok_or_else(|| (LexErrorKind::MissingEndingQuote, input))?
                {
                    '\\' => {
                        let input = iter.as_str();
                        let c = iter.next().unwrap_or('\0');
                        res.push(match c {
                            '"' | '\\' => c,
                            'x' => {
                                let (b, input) = hex_byte(iter.as_str())?;
                                iter = input.chars();
                                b as char
                            }
                            '0'...'7' => {
                                let (b, input) = oct_byte(input)?;
                                iter = input.chars();
                                b as char
                            }
                            _ => {
                                return Err((
                                    LexErrorKind::InvalidCharacterEscape,
                                    &input[..c.len_utf8()],
                                ));
                            }
                        });
                    }
                    '"' => return Ok((res.into(), iter.as_str())),
                    c => res.push(c),
                };
            }
        } else {
            let mut res = Vec::new();
            loop {
                let (b, rest) = hex_byte(input)?;
                res.push(b);
                input = rest;
                if let Ok((_, rest)) = ByteSeparator::lex(input) {
                    input = rest;
                } else {
                    return Ok((res.into(), input));
                }
            }
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
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("4x", 16).unwrap_err(),
            radix: 16,
        },
        "4x"
    );

    assert_ok!(Bytes::lex("01;"), Bytes::from(vec![0x01]), ";");

    assert_ok!(Bytes::lex("01:2f-34"), Bytes::from(vec![0x01, 0x2F, 0x34]));

    assert_err!(Bytes::lex("\"1"), LexErrorKind::MissingEndingQuote, "1");

    assert_err!(
        Bytes::lex(r#""\n""#),
        LexErrorKind::InvalidCharacterEscape,
        "n"
    );
}
