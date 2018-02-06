use lex::{expect, hex_byte, oct_byte, Lex, LexErrorKind, LexResult};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::{self, Visitor};

use std::borrow::Cow;
use std::fmt::{self, Debug, Formatter};
use std::ops::Deref;
use std::str;

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum Bytes<'a> {
    Str(Cow<'a, str>),
    Raw(Cow<'a, [u8]>),
}

impl<'a> Serialize for Bytes<'a> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        match *self {
            Bytes::Str(ref s) => s.serialize(ser),
            Bytes::Raw(ref b) => b.serialize(ser),
        }
    }
}

impl<'a, 'de: 'a> Deserialize<'de> for Bytes<'a> {
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        struct BytesVisitor;

        impl<'de> Visitor<'de> for BytesVisitor {
            type Value = Bytes<'de>;

            fn expecting(&self, f: &mut Formatter) -> fmt::Result {
                f.write_str("a byte buffer or a string")
            }

            fn visit_bytes<E: de::Error>(self, v: &[u8]) -> Result<Bytes<'de>, E> {
                self.visit_byte_buf(v.into())
            }

            fn visit_borrowed_bytes<E: de::Error>(self, v: &'de [u8]) -> Result<Bytes<'de>, E> {
                Ok(Bytes::from(v))
            }

            fn visit_byte_buf<E: de::Error>(self, v: Vec<u8>) -> Result<Bytes<'de>, E> {
                Ok(Bytes::from(v))
            }

            fn visit_str<E: de::Error>(self, v: &str) -> Result<Bytes<'de>, E> {
                self.visit_string(v.into())
            }

            fn visit_borrowed_str<E: de::Error>(self, v: &'de str) -> Result<Bytes<'de>, E> {
                Ok(Bytes::from(v))
            }

            fn visit_string<E: de::Error>(self, v: String) -> Result<Bytes<'de>, E> {
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

impl<'a> Bytes<'a> {
    pub fn contains(&self, rhs: &[u8]) -> bool {
        unsafe { !memmem(self.as_ptr(), self.len(), rhs.as_ptr(), rhs.len()).is_null() }
    }
}

impl<'a> From<&'a [u8]> for Bytes<'a> {
    fn from(src: &'a [u8]) -> Self {
        Bytes::Raw(Cow::from(src))
    }
}

impl<'a> From<Vec<u8>> for Bytes<'a> {
    fn from(src: Vec<u8>) -> Self {
        Bytes::Raw(Cow::from(src))
    }
}

impl<'a> From<&'a str> for Bytes<'a> {
    fn from(src: &'a str) -> Self {
        Bytes::Str(Cow::from(src))
    }
}

impl<'a> From<String> for Bytes<'a> {
    fn from(src: String) -> Self {
        Bytes::Str(Cow::from(src))
    }
}

impl<'a> Debug for Bytes<'a> {
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

impl<'a> Deref for Bytes<'a> {
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

impl<'a, 'i> Lex<'i> for Bytes<'a> {
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
