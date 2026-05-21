use crate::lex::{LexErrorKind, LexResult, LexWith, span};
use crate::rhs_types::bytes::lex_raw_string_as_str;
use crate::{Compare, ExecutionContext, FilterParser, LhsValue};
use cfg_if::cfg_if;
use serde::{Serialize, Serializer};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use thiserror::Error;

cfg_if! {
    if #[cfg(feature = "regex")] {
        mod imp_real;
        pub use self::imp_real::*;
    } else {
        mod imp_stub;
        pub use self::imp_stub::*;
    }
}

/// RegexFormat describes the format behind the regex
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum RegexFormat {
    /// Literal string was used to define the expression
    Literal,
    /// Raw string was used to define the expression
    Raw(u8),
}

impl PartialEq for Regex {
    fn eq(&self, other: &Regex) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Regex {}

impl Hash for Regex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl Display for Regex {
    /// Shows the original regular expression.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for Regex {
    /// Shows the original regular expression.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Regex")
            .field("pattern", &self.as_str())
            .field("format", &self.format())
            .finish()
    }
}

fn lex_regex_from_raw_string<'i>(
    input: &'i str,
    parser: &FilterParser<'_>,
) -> LexResult<'i, Regex> {
    let ((lexed, hashes), input) = lex_raw_string_as_str(input)?;
    match Regex::new(lexed, RegexFormat::Raw(hashes), parser.settings()) {
        Ok(regex) => Ok((regex, input)),
        Err(err) => Err((LexErrorKind::ParseRegex(err), input)),
    }
}

fn lex_regex_from_literal<'i>(input: &'i str, parser: &FilterParser<'_>) -> LexResult<'i, Regex> {
    let mut regex_buf = String::new();
    let mut in_char_class = false;
    let (regex_str, input) = {
        let mut iter = input.chars();
        loop {
            let before_char = iter.as_str();
            match iter
                .next()
                .ok_or((LexErrorKind::MissingEndingQuote, input))?
            {
                '\\' => {
                    if let Some(c) = iter.next() {
                        if in_char_class || c != '"' {
                            regex_buf.push('\\');
                        }
                        regex_buf.push(c);
                    }
                }
                '"' if !in_char_class => {
                    break (span(input, before_char), iter.as_str());
                }
                '[' if !in_char_class => {
                    in_char_class = true;
                    regex_buf.push('[');
                }
                ']' if in_char_class => {
                    in_char_class = false;
                    regex_buf.push(']');
                }
                c => {
                    regex_buf.push(c);
                }
            };
        }
    };
    match Regex::new(&regex_buf, RegexFormat::Literal, parser.settings()) {
        Ok(regex) => Ok((regex, input)),
        Err(err) => Err((LexErrorKind::ParseRegex(err), regex_str)),
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for Regex {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        if let Some(c) = input.as_bytes().first() {
            match c {
                b'"' => lex_regex_from_literal(&input[1..], parser),
                b'r' => lex_regex_from_raw_string(&input[1..], parser),
                _ => Err((LexErrorKind::ExpectedLiteral("\" or r"), input)),
            }
        } else {
            Err((LexErrorKind::EOF, input))
        }
    }
}

impl Serialize for Regex {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.as_str().serialize(ser)
    }
}

/// An error that occurred during parsing or compiling a regular expression.
#[non_exhaustive]
#[derive(Clone, Debug, Error, PartialEq)]
pub enum Error {
    /// A syntax error.
    #[error("{0}")]
    Syntax(String),
    /// The compiled regex exceeded the configured
    /// regex compiled size limit.
    #[error("Compiled regex exceeds size limit of {0} bytes.")]
    CompiledTooBig(usize),
    /// An uncategorized error.
    #[error("{0}")]
    Other(String),
}

impl<U> Compare<U> for Regex {
    #[inline]
    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
        self.is_match(match value {
            LhsValue::Bytes(bytes) => bytes,
            _ => unreachable!(),
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{ParserSettings, SchemeBuilder};

    #[test]
    fn test() {
        let scheme = SchemeBuilder::new().build();
        let parser = FilterParser::new(&scheme);

        let expr = assert_ok!(
            Regex::lex_with(r#""[a-z"\]]+\d{1,10}\"";"#, &parser),
            Regex::new(
                r#"[a-z"\]]+\d{1,10}""#,
                RegexFormat::Literal,
                &ParserSettings::default(),
            )
            .unwrap(),
            ";"
        );

        assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

        assert_err!(
            Regex::lex_with(r#""abcd\"#, &parser),
            LexErrorKind::MissingEndingQuote,
            "abcd\\"
        );
    }

    #[test]
    fn test_raw_string() {
        let scheme = SchemeBuilder::new().build();
        let parser = FilterParser::new(&scheme);

        let expr = assert_ok!(
            Regex::lex_with(
                r###"r#"[a-z"\]]+\d{1,10}""#;"###,
                &FilterParser::new(&scheme)
            ),
            Regex::new(
                r#"[a-z"\]]+\d{1,10}""#,
                RegexFormat::Raw(1),
                parser.settings(),
            )
            .unwrap(),
            ";"
        );

        assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

        let expr = assert_ok!(
            Regex::lex_with(
                r##"r#"(?u)\*\a\f\t\n\r\v\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#"##,
                &parser,
            ),
            Regex::new(
                r#"(?u)\*\a\f\t\n\r\v\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#,
                RegexFormat::Raw(1),
                parser.settings(),
            )
            .unwrap(),
            ""
        );

        assert_json!(
            expr,
            r#"(?u)\*\a\f\t\n\r\v\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#
        );

        assert_err!(
            Regex::lex_with("x", &FilterParser::new(&scheme)),
            LexErrorKind::ExpectedLiteral("\" or r"),
            "x"
        );
    }
}
