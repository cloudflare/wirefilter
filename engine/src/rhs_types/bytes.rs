use crate::lex::{Lex, LexErrorKind, LexResult, take};
use crate::strict_partial_ord::StrictPartialOrd;
use serde::{Serialize, Serializer};
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::str;

/// BytesFormat describes the format in which the string was expressed
#[derive(PartialEq, Eq, Copy, Clone)]
pub enum BytesFormat {
    /// Quoted string
    Quoted,
    /// Raw string, similar to rust raw strings
    Raw(u8), // For the hash count
    /// Raw byte string literal
    Byte,
}

/// Bytes literal represented either by a string, raw string or raw bytes.
#[derive(PartialEq, Eq, Clone)]
pub struct BytesExpr {
    format: BytesFormat,
    data: Box<[u8]>,
}

impl BytesExpr {
    /// Creates a new bytes literal.
    #[inline]
    pub fn new(data: impl Into<Box<[u8]>>, format: BytesFormat) -> Self {
        Self {
            format,
            data: data.into(),
        }
    }

    /// Returns the Bytes format based on the BytesFormat enum
    #[inline]
    pub fn format(&self) -> BytesFormat {
        self.format
    }
}

impl Serialize for BytesExpr {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match self.format() {
            BytesFormat::Quoted | BytesFormat::Raw(_) => match str::from_utf8(&self.data) {
                Ok(s) => s.serialize(serializer),
                Err(_) => self.data.serialize(serializer),
            },
            BytesFormat::Byte => self.data.serialize(serializer),
        }
    }
}

// We need custom `Hash` consistent with `Borrow` invariants.
// We can get away with `Eq` invariant though because we do want
// `Bytes == Bytes` to check enum tags but `Bytes == &[u8]` to ignore them, and
// consistency of the latter is all that matters for `Borrow` consumers.
impl Hash for BytesExpr {
    #[inline]
    fn hash<H: Hasher>(&self, h: &mut H) {
        (self as &[u8]).hash(h);
    }
}

impl From<Vec<u8>> for BytesExpr {
    #[inline]
    fn from(src: Vec<u8>) -> Self {
        Self {
            format: BytesFormat::Byte,
            data: src.into_boxed_slice(),
        }
    }
}

impl From<String> for BytesExpr {
    #[inline]
    fn from(src: String) -> Self {
        Self {
            format: BytesFormat::Quoted,
            data: src.into_boxed_str().into_boxed_bytes(),
        }
    }
}

impl From<BytesExpr> for Box<[u8]> {
    #[inline]
    fn from(bytes: BytesExpr) -> Self {
        bytes.data
    }
}

impl From<BytesExpr> for Vec<u8> {
    #[inline]
    fn from(bytes: BytesExpr) -> Self {
        bytes.data.into_vec()
    }
}

impl Debug for BytesExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        fn fmt_raw(data: &[u8], f: &mut Formatter<'_>) -> fmt::Result {
            let mut iter = data.iter();
            if let Some(&first) = iter.next() {
                write!(f, "{first:02X}")?;
                for &b in iter {
                    write!(f, ":{b:02X}")?;
                }
            }
            Ok(())
        }

        match self.format {
            BytesFormat::Quoted | BytesFormat::Raw(_) => match str::from_utf8(&self.data) {
                Ok(s) => s.fmt(f),
                Err(_) => fmt_raw(&self.data, f),
            },
            BytesFormat::Byte => fmt_raw(&self.data, f),
        }
    }
}

impl Deref for BytesExpr {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        &self.data
    }
}

impl AsRef<[u8]> for BytesExpr {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl<'a> IntoIterator for &'a BytesExpr {
    type IntoIter = std::slice::Iter<'a, u8>;
    type Item = &'a u8;

    #[inline]
    fn into_iter(self) -> std::slice::Iter<'a, u8> {
        self.iter()
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

fn write_char(vec: &mut Vec<u8>, c: char) {
    let mut bytes = [0; 4];
    let len = c.encode_utf8(&mut bytes).len();
    vec.extend_from_slice(&bytes[..len]);
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Serialize)]
enum ByteSeparator {
    Colon,
    Dash,
    Dot,
}

impl Lex<'_> for ByteSeparator {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let (sep, rest) = take(input, 1)?;
        match sep {
            ":" => Ok((ByteSeparator::Colon, rest)),
            "-" => Ok((ByteSeparator::Dash, rest)),
            "." => Ok((ByteSeparator::Dot, rest)),
            _ => Err((LexErrorKind::ExpectedName("byte separator"), sep)),
        }
    }
}

pub(crate) fn lex_quoted_string_as_vec(input: &str) -> LexResult<'_, Vec<u8>> {
    let full_input = input;
    let mut res = Vec::new();
    let mut iter = input.chars();
    loop {
        match iter
            .next()
            .ok_or((LexErrorKind::MissingEndingQuote, full_input))?
        {
            '\\' => {
                let input = iter.as_str();

                let c = iter
                    .next()
                    .ok_or((LexErrorKind::MissingEndingQuote, full_input))?;

                match c {
                    '"' | '\\' => write_char(&mut res, c),
                    'x' => {
                        let (b, rest) = hex_byte(iter.as_str())?;
                        iter = rest.chars();
                        res.push(b);
                    }
                    '0'..='7' => {
                        let (b, rest) = oct_byte(input)?;
                        iter = rest.chars();
                        res.push(b);
                    }
                    _ => {
                        return Err((LexErrorKind::InvalidCharacterEscape, &input[..c.len_utf8()]));
                    }
                }
            }
            '"' => return Ok((res, iter.as_str())),
            c => write_char(&mut res, c),
        };
    }
}

fn lex_quoted_string(input: &str) -> LexResult<'_, BytesExpr> {
    lex_quoted_string_as_vec(input).map(|(vec, rest)| {
        let bytes = BytesExpr {
            format: BytesFormat::Quoted,
            data: vec.into_boxed_slice(),
        };

        (bytes, rest)
    })
}

fn lex_byte_string(mut input: &str) -> LexResult<'_, BytesExpr> {
    let mut res = Vec::new();
    let (b, rest) = hex_byte(input)?;
    res.push(b);
    input = rest;
    let (_, rest) = ByteSeparator::lex(input)?;
    input = rest;
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

pub(crate) fn lex_raw_string_as_str(input: &str) -> LexResult<'_, (&str, u8)> {
    let full_input = input;

    let start_hash_count = input.chars().take_while(|&c| c == '#').count();
    let hash_count: u8 = start_hash_count
        .try_into()
        .map_err(|_| (LexErrorKind::InvalidRawStringHashCount, full_input))?;

    // consume '"'`
    if input.as_bytes().get(start_hash_count) != Some(&b'"') {
        return Err((
            LexErrorKind::ExpectedName("\" or #"),
            &full_input[start_hash_count..],
        ));
    }

    let mut iter = input[start_hash_count + 1..].char_indices().peekable();

    // look for final sequence or fail
    loop {
        let (i, c) = iter
            .next()
            .ok_or((LexErrorKind::MissingEndingQuote, full_input))?;
        if c == '"' {
            // count end hashes
            let mut end_hash_count = 0;
            while iter.by_ref().next_if(|(_, x)| x == &'#').is_some() {
                end_hash_count += 1;
            }

            // return if this is a final sequence
            if end_hash_count >= start_hash_count {
                let full_prefix = start_hash_count + 1;
                return Ok((
                    (&full_input[full_prefix..i + full_prefix], hash_count),
                    &full_input[2 * full_prefix + i..],
                ));
            }
        }
    }
}

#[inline]
fn lex_raw_string(input: &str) -> LexResult<'_, BytesExpr> {
    let ((lexed, hash_count), rest) = lex_raw_string_as_str(input)?;
    Ok((
        BytesExpr {
            format: BytesFormat::Raw(hash_count),
            data: Box::from(lexed.as_bytes()),
        },
        rest,
    ))
}

pub(crate) fn lex_quoted_or_raw_string(input: &str) -> LexResult<'_, BytesExpr> {
    match input.as_bytes().first() {
        Some(b'"') => lex_quoted_string(&input[1..]),
        Some(b'r') => lex_raw_string(&input[1..]),
        Some(_) => Err((LexErrorKind::ExpectedName("\" or r"), input)),
        None => Err((LexErrorKind::EOF, input)),
    }
}

impl Lex<'_> for BytesExpr {
    #[inline]
    fn lex(input: &str) -> LexResult<'_, Self> {
        match input.as_bytes().first() {
            Some(b'"' | b'r') => lex_quoted_or_raw_string(input),
            Some(_) => lex_byte_string(input),
            None => Err((LexErrorKind::EOF, input)),
        }
    }
}

impl StrictPartialOrd for [u8] {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test() {
        assert_ok!(
            BytesExpr::lex("01:2e:f3-77.12;"),
            BytesExpr::from(vec![0x01, 0x2E, 0xF3, 0x77, 0x12]),
            ";"
        );

        assert_ok!(
            BytesExpr::lex(r#""s\\t\"r\x0A\000t""#),
            BytesExpr::from("s\\t\"r\n\0t".to_owned())
        );

        assert_err!(
            BytesExpr::lex("01:4x;"),
            LexErrorKind::ParseInt {
                err: u8::from_str_radix("4x", 16).unwrap_err(),
                radix: 16,
            },
            "4x"
        );

        assert_err!(
            BytesExpr::lex("01;"),
            LexErrorKind::ExpectedName("byte separator"),
            ";"
        );

        assert_err!(
            BytesExpr::lex("01:;"),
            LexErrorKind::CountMismatch {
                name: "character",
                actual: 1,
                expected: 2
            },
            ";"
        );

        assert_ok!(
            BytesExpr::lex("01:2f-34"),
            BytesExpr::from(vec![0x01, 0x2F, 0x34])
        );

        assert_err!(BytesExpr::lex("\"1"), LexErrorKind::MissingEndingQuote, "1");

        assert_err!(
            BytesExpr::lex(r#""\n""#),
            LexErrorKind::InvalidCharacterEscape,
            "n"
        );

        assert_err!(
            BytesExpr::lex(r#""abcd\"#),
            LexErrorKind::MissingEndingQuote,
            "abcd\\"
        );

        assert_err!(
            BytesExpr::lex(r#""\01😢""#),
            LexErrorKind::ParseInt {
                err: u8::from_str_radix("01😢", 8).unwrap_err(),
                radix: 8,
            },
            "01😢"
        );

        assert_err!(
            BytesExpr::lex(r#""\x3😢""#),
            LexErrorKind::ParseInt {
                err: u8::from_str_radix("3😢", 16).unwrap_err(),
                radix: 16,
            },
            "3😢"
        );

        assert_err!(
            BytesExpr::lex("12:3😢"),
            LexErrorKind::ParseInt {
                err: u8::from_str_radix("3😢", 16).unwrap_err(),
                radix: 16,
            },
            "3😢"
        );

        assert_ok!(
            BytesExpr::lex(r#""\x7F""#),
            BytesExpr::from("\x7F".to_owned())
        );

        assert_ok!(
            BytesExpr::lex(r#""\x80""#),
            BytesExpr::new(vec![0x80], BytesFormat::Quoted)
        );

        assert_ok!(
            BytesExpr::lex(r#""\xFF""#),
            BytesExpr::new(vec![0xFF], BytesFormat::Quoted)
        );

        assert_ok!(
            BytesExpr::lex(r#""\177""#),
            BytesExpr::from("\x7F".to_owned())
        );

        assert_ok!(
            BytesExpr::lex(r#""\200""#),
            BytesExpr::new(vec![0x80], BytesFormat::Quoted)
        );

        assert_ok!(
            BytesExpr::lex(r#""\377""#),
            BytesExpr::new(vec![0xFF], BytesFormat::Quoted)
        );

        assert_ok!(
            BytesExpr::lex("c2:b4710c6888a5d47befe865c8e6fb19"),
            BytesExpr::from(vec![0xC2, 0xb4]),
            "710c6888a5d47befe865c8e6fb19"
        );
    }

    #[test]
    fn test_raw_string() {
        // Valid empty strings
        assert_ok!(
            BytesExpr::lex("r\"\""),
            BytesExpr::new("".as_bytes(), BytesFormat::Raw(0))
        );
        assert_ok!(
            BytesExpr::lex("r#\"\"#"),
            BytesExpr::new("".as_bytes(), BytesFormat::Raw(1))
        );
        assert_ok!(
            BytesExpr::lex("r##\"\"##"),
            BytesExpr::new("".as_bytes(), BytesFormat::Raw(2))
        );
        assert_ok!(
            BytesExpr::lex("r###\"\"###"),
            BytesExpr::new("".as_bytes(), BytesFormat::Raw(3))
        );

        // Valid raw strings
        assert_ok!(
            BytesExpr::lex("r\"a\""),
            BytesExpr::new("a".as_bytes(), BytesFormat::Raw(0))
        );
        assert_ok!(
            BytesExpr::lex("r#\"a\"#"),
            BytesExpr::new("a".as_bytes(), BytesFormat::Raw(1))
        );
        assert_ok!(
            BytesExpr::lex("r##\"a\"##"),
            BytesExpr::new("a".as_bytes(), BytesFormat::Raw(2))
        );
        assert_ok!(
            BytesExpr::lex("r###\"a\"###"),
            BytesExpr::new("a".as_bytes(), BytesFormat::Raw(3))
        );

        // Quotes and hashes can be used inside the raw string
        assert_ok!(
            BytesExpr::lex("r\"#\""),
            BytesExpr::new("#".as_bytes(), BytesFormat::Raw(0))
        );
        assert_ok!(
            BytesExpr::lex("r\"a#\""),
            BytesExpr::new("a#".as_bytes(), BytesFormat::Raw(0))
        );
        assert_ok!(
            BytesExpr::lex("r#\"\"a\"\"\"#"),
            BytesExpr::new("\"a\"\"".as_bytes(), BytesFormat::Raw(1))
        );
        assert_ok!(
            BytesExpr::lex("r##\"\"a\"#b\"##"),
            BytesExpr::new("\"a\"#b".as_bytes(), BytesFormat::Raw(2))
        );
        assert_ok!(
            BytesExpr::lex("r###\"a###\"##\"\"###"),
            BytesExpr::new("a###\"##\"".as_bytes(), BytesFormat::Raw(3))
        );
        assert_ok!(
            BytesExpr::lex("r#\"a\"\"\"#"),
            BytesExpr::new("a\"\"".as_bytes(), BytesFormat::Raw(1))
        );
        assert_ok!(
            BytesExpr::lex("r##\"a\"#\"##"),
            BytesExpr::new("a\"#".as_bytes(), BytesFormat::Raw(2))
        );
        assert_ok!(
            BytesExpr::lex("r###\"a###\"##\"###"),
            BytesExpr::new("a###\"##".as_bytes(), BytesFormat::Raw(3))
        );

        // Expect an error if the number of '#' doesn't match
        assert_err!(
            BytesExpr::lex("r#\"a\""),
            LexErrorKind::MissingEndingQuote,
            "#\"a\""
        );
        assert_err!(
            BytesExpr::lex("r##\"a\"#"),
            LexErrorKind::MissingEndingQuote,
            "##\"a\"#"
        );
        assert_err!(
            BytesExpr::lex("r###\"a\"##"),
            LexErrorKind::MissingEndingQuote,
            "###\"a\"##"
        );

        // Expect an error when there are too many hashes being used
        let hashes = format!("r{}\"abc\"{}", "#".repeat(255), "#".repeat(255));
        assert_ok!(
            BytesExpr::lex(hashes.as_str()),
            BytesExpr::new("abc".as_bytes(), BytesFormat::Raw(255))
        );
        let hashes = format!("r{}\"abc\"{}", "#".repeat(256), "#".repeat(256));
        assert_err!(
            BytesExpr::lex(hashes.as_str()),
            LexErrorKind::InvalidRawStringHashCount,
            &hashes.as_str()[1..]
        );

        // Test regex escapes remain the same
        assert_ok!(
            BytesExpr::lex(r#"r".\d\D\pA\p{Greek}\PA\P{Greek}[xyz][^xyz][a-z][[:alpha:]][[:^alpha:]][x[^xyz]][a-y&&xyz][0-9&&[^4]][0-9--4][a-g~~b-h][\[\]]""#),
            BytesExpr::new(r#".\d\D\pA\p{Greek}\PA\P{Greek}[xyz][^xyz][a-z][[:alpha:]][[:^alpha:]][x[^xyz]][a-y&&xyz][0-9&&[^4]][0-9--4][a-g~~b-h][\[\]]"#.as_bytes(), BytesFormat::Raw(0))
        );
        assert_ok!(
            BytesExpr::lex(
                r##"r#"\*\a\f\t\n\r\v\123\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#"##
            ),
            BytesExpr::new(
                r#"\*\a\f\t\n\r\v\123\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#.as_bytes(),
                BytesFormat::Raw(1)
            )
        );

        // Invalid character after 'r' or '#'
        assert_err!(
            BytesExpr::lex("r"),
            LexErrorKind::ExpectedName("\" or #"),
            ""
        );
        assert_err!(
            BytesExpr::lex("r#ab"),
            LexErrorKind::ExpectedName("\" or #"),
            "ab"
        );
        assert_err!(
            BytesExpr::lex("r##ab"),
            LexErrorKind::ExpectedName("\" or #"),
            "ab"
        );

        // Any characters after a raw string should get returned
        assert_eq!(
            BytesExpr::lex("r#\"ab\"##"),
            Ok((BytesExpr::new("ab".as_bytes(), BytesFormat::Raw(1)), "#"))
        );
        assert_eq!(
            BytesExpr::lex("r#\"ab\"#\""),
            Ok((BytesExpr::new("ab".as_bytes(), BytesFormat::Raw(1)), "\""))
        );
        assert_eq!(
            BytesExpr::lex("r#\"ab\"#a"),
            Ok((BytesExpr::new("ab".as_bytes(), BytesFormat::Raw(1)), "a"))
        );
    }
}
