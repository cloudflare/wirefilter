use crate::{
    lex::{expect, take, Lex, LexErrorKind, LexResult},
    strict_partial_ord::StrictPartialOrd,
};
use serde::Serialize;
use std::{
    borrow::Borrow,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    ops::Deref,
    str,
};

#[derive(PartialEq, Eq, Clone, Serialize)]
#[serde(untagged)]
pub enum Bytes {
    Str(Box<str>),
    Raw(Box<[u8]>),
}

// We need custom `Hash` consistent with `Borrow` invariants.
// We can get away with `Eq` invariant though because we do want
// `Bytes == Bytes` to check enum tags but `Bytes == &[u8]` to ignore them, and
// consistency of the latter is all that matters for `Borrow` consumers.
#[allow(clippy::derive_hash_xor_eq)]
impl Hash for Bytes {
    fn hash<H: Hasher>(&self, h: &mut H) {
        (self as &[u8]).hash(h)
    }
}

impl From<Vec<u8>> for Bytes {
    fn from(src: Vec<u8>) -> Self {
        Bytes::Raw(src.into_boxed_slice())
    }
}

impl From<String> for Bytes {
    fn from(src: String) -> Self {
        Bytes::Str(src.into_boxed_str())
    }
}

impl From<Bytes> for Box<[u8]> {
    fn from(bytes: Bytes) -> Self {
        match bytes {
            Bytes::Str(s) => s.into_boxed_bytes(),
            Bytes::Raw(b) => b,
        }
    }
}

impl From<Bytes> for Vec<u8> {
    fn from(bytes: Bytes) -> Self {
        match bytes {
            Bytes::Str(s) => s.into_boxed_bytes().into_vec(),
            Bytes::Raw(b) => b.into_vec(),
        }
    }
}

impl Debug for Bytes {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Bytes::Str(s) => s.fmt(f),
            Bytes::Raw(b) => {
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
        match self {
            Bytes::Str(s) => s.as_bytes(),
            Bytes::Raw(b) => b,
        }
    }
}

impl Borrow<[u8]> for Bytes {
    fn borrow(&self) -> &[u8] {
        self
    }
}

fn fixed_byte(input: &str, digits: usize, radix: u32) -> LexResult<'_, u8> {
    let (digits, rest) = take(input, digits)?;
    match u8::from_str_radix(digits, radix) {
        Ok(b) => Ok((b, rest)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, digits)),
    }
}

fn hex_byte(input: &str) -> LexResult<'_, u8> {
    fixed_byte(input, 2, 16)
}

fn oct_byte(input: &str) -> LexResult<'_, u8> {
    fixed_byte(input, 3, 8)
}

lex_enum!(ByteSeparator {
    ":" => Colon,
    "-" => Dash,
    "." => Dot,
});

impl<'i> Lex<'i> for Bytes {
    fn lex(mut input: &str) -> LexResult<'_, Self> {
        if let Ok(input) = expect(input, "\"") {
            let full_input = input;
            let mut res = String::new();
            let mut iter = input.chars();
            loop {
                match iter
                    .next()
                    .ok_or_else(|| (LexErrorKind::MissingEndingQuote, full_input))?
                {
                    '\\' => {
                        let input = iter.as_str();

                        let c = iter
                            .next()
                            .ok_or_else(|| (LexErrorKind::MissingEndingQuote, full_input))?;

                        res.push(match c {
                            '"' | '\\' => c,
                            'x' => {
                                let (b, input) = hex_byte(iter.as_str())?;
                                iter = input.chars();
                                b as char
                            }
                            '0'..='7' => {
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

impl StrictPartialOrd for [u8] {}

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

    assert_err!(
        Bytes::lex(r#""abcd\"#),
        LexErrorKind::MissingEndingQuote,
        "abcd\\"
    );

    assert_err!(
        Bytes::lex(r#""\01😢""#),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("01😢", 8).unwrap_err(),
            radix: 8,
        },
        "01😢"
    );

    assert_err!(
        Bytes::lex(r#""\x3😢""#),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("3😢", 16).unwrap_err(),
            radix: 16,
        },
        "3😢"
    );

    assert_err!(
        Bytes::lex("12:3😢"),
        LexErrorKind::ParseInt {
            err: u8::from_str_radix("3😢", 16).unwrap_err(),
            radix: 16,
        },
        "3😢"
    );
}
