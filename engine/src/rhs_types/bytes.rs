use lex::{expect, take, Lex, LexErrorKind, LexResult};
use std::{
    borrow::Borrow,
    fmt::{self, Debug, Formatter},
    iter::Cloned,
    ops::Deref,
    slice::Iter,
    str,
};
use strict_partial_ord::StrictPartialOrd;

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Serialize)]
pub struct Bytes(Box<[u8]>);

impl From<Vec<u8>> for Bytes {
    fn from(src: Vec<u8>) -> Self {
        Bytes(src.into_boxed_slice())
    }
}

impl From<String> for Bytes {
    fn from(src: String) -> Self {
        src.into_bytes().into()
    }
}

impl Bytes {
    fn iter(&self) -> <&Self as IntoIterator>::IntoIter {
        self.into_iter()
    }
}

impl Debug for Bytes {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "\"")?;
        for b in self {
            #[cfg_attr(feature = "cargo-clippy", allow(match_overlapping_arm))]
            match b {
                b'"' => write!(f, r#"\""#),
                b'\\' => write!(f, r#"\"#),
                0x20...0x7E => write!(f, "{}", b as char),
                _ => write!(f, r#"\x{:02X}"#, b),
            }?;
        }
        write!(f, "\" (")?;
        for (i, b) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ":")?;
            }
            write!(f, "{:02X}", b)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl Deref for Bytes {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8]> for Bytes {
    fn borrow(&self) -> &[u8] {
        self
    }
}

impl<'a> IntoIterator for &'a Bytes {
    type IntoIter = Cloned<Iter<'a, u8>>;
    type Item = u8;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().cloned()
    }
}

fn fixed_byte(input: &str, digits: usize, radix: u32) -> LexResult<u8> {
    let (digits, rest) = take(input, digits)?;
    match u8::from_str_radix(digits, radix) {
        Ok(b) => Ok((b, rest)),
        Err(err) => Err((LexErrorKind::ParseInt { err, radix }, digits)),
    }
}

fn hex_byte(input: &str) -> LexResult<u8> {
    fixed_byte(input, 2, 16)
}

fn oct_byte(input: &str) -> LexResult<u8> {
    fixed_byte(input, 3, 8)
}

lex_enum!(ByteSeparator {
    ":" => Colon,
    "-" => Dash,
    "." => Dot,
});

impl<'i> Lex<'i> for Bytes {
    fn lex(mut input: &str) -> LexResult<Self> {
        if let Ok(input) = expect(input, "\"") {
            let mut res = String::new();
            let mut iter = input.chars();
            loop {
                match iter
                    .next()
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
}
