use crate::lex::{LexErrorKind, LexResult, LexWith, span};
use crate::rhs_types::bytes::lex_raw_string_as_str;
use crate::{Compare, ExecutionContext, FilterParser, LhsValue};
use cfg_if::cfg_if;
use serde::{Serialize, Serializer};
use std::fmt::{self, Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::sync::Arc;
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

/// Regex expression.
#[derive(Clone)]
pub struct RegexExpr {
    pattern: Arc<str>,
    format: RegexFormat,
    regex: Arc<dyn Regex>,
}

impl RegexExpr {
    /// Create a new regex expression.
    pub fn new(
        pattern: &str,
        format: RegexFormat,
        provider: &impl RegexProvider,
    ) -> Result<Self, Error> {
        provider.lookup_regex(pattern).map(|regex| Self {
            pattern: pattern.to_owned().into(),
            format,
            regex,
        })
    }
    /// Returns the pattern of this regex.
    #[inline]
    pub fn as_str(&self) -> &str {
        &self.pattern
    }

    /// Returns the format used by the pattern.
    #[inline]
    pub fn format(&self) -> RegexFormat {
        self.format
    }

    /// Returns the associated regex object.
    #[inline]
    pub fn as_regex(&self) -> &Arc<dyn Regex> {
        &self.regex
    }

    /// Converts the regex expression into its underlying regex object.
    #[inline]
    pub fn into_regex(self) -> Arc<dyn Regex> {
        self.regex
    }
}

impl PartialEq for RegexExpr {
    fn eq(&self, other: &RegexExpr) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for RegexExpr {}

impl Hash for RegexExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state);
    }
}

impl Display for RegexExpr {
    /// Shows the original regular expression.
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(self.as_str(), f)
    }
}

impl Debug for RegexExpr {
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
) -> LexResult<'i, RegexExpr> {
    let ((lexed, hashes), input) = lex_raw_string_as_str(input)?;
    match RegexExpr::new(
        lexed,
        RegexFormat::Raw(hashes),
        &parser.settings().regex_provider,
    ) {
        Ok(regex) => Ok((regex, input)),
        Err(err) => Err((LexErrorKind::ParseRegex(err), input)),
    }
}

fn lex_regex_from_literal<'i>(
    input: &'i str,
    parser: &FilterParser<'_>,
) -> LexResult<'i, RegexExpr> {
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
    match RegexExpr::new(
        &regex_buf,
        RegexFormat::Literal,
        &parser.settings().regex_provider,
    ) {
        Ok(regex) => Ok((regex, input)),
        Err(err) => Err((LexErrorKind::ParseRegex(err), regex_str)),
    }
}

impl<'i, 's> LexWith<'i, &FilterParser<'s>> for RegexExpr {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Self> {
        if let Some(c) = input.as_bytes().first() {
            match c {
                b'"' => lex_regex_from_literal(&input[1..], parser),
                b'r' => lex_regex_from_raw_string(&input[1..], parser),
                _ => Err((LexErrorKind::ExpectedName("\" or r"), input)),
            }
        } else {
            Err((LexErrorKind::EOF, input))
        }
    }
}

impl Serialize for RegexExpr {
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

/// Trait representing a compiled regex object.
pub trait Regex: Send + Sync {
    /// Matches the regex against some input.
    fn is_match(&self, input: &[u8]) -> bool;
}

impl<U> Compare<U> for Arc<dyn Regex> {
    #[inline]
    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
        self.is_match(match value {
            LhsValue::Bytes(bytes) => bytes,
            _ => unreachable!(),
        })
    }
}

/// Regex provider.
pub trait RegexProvider: Debug + Send + Sync {
    /// Attempts to retrieve a regex from the provider.
    fn lookup_regex(&self, pattern: &str) -> Result<Arc<dyn Regex>, Error>;
}

impl RegexProvider for Arc<dyn RegexProvider> {
    #[inline]
    fn lookup_regex(&self, pattern: &str) -> Result<Arc<dyn Regex>, Error> {
        (**self).lookup_regex(pattern)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::SchemeBuilder;

    #[test]
    fn test() {
        let scheme = SchemeBuilder::new().build();
        let parser = FilterParser::new(&scheme);

        let expr = assert_ok!(
            RegexExpr::lex_with(r#""[a-z"\]]+\d{1,10}\"";"#, &parser),
            RegexExpr::new(
                r#"[a-z"\]]+\d{1,10}""#,
                RegexFormat::Literal,
                &parser.settings().regex_provider,
            )
            .unwrap(),
            ";"
        );

        assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

        assert_err!(
            RegexExpr::lex_with(r#""abcd\"#, &parser),
            LexErrorKind::MissingEndingQuote,
            "abcd\\"
        );
    }

    #[test]
    fn test_raw_string() {
        let scheme = SchemeBuilder::new().build();
        let parser = FilterParser::new(&scheme);

        let expr = assert_ok!(
            RegexExpr::lex_with(
                r###"r#"[a-z"\]]+\d{1,10}""#;"###,
                &FilterParser::new(&scheme)
            ),
            RegexExpr::new(
                r#"[a-z"\]]+\d{1,10}""#,
                RegexFormat::Raw(1),
                &parser.settings().regex_provider,
            )
            .unwrap(),
            ";"
        );

        assert_json!(expr, r#"[a-z"\]]+\d{1,10}""#);

        let expr = assert_ok!(
            RegexExpr::lex_with(
                r##"r#"(?u)\*\a\f\t\n\r\v\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#"##,
                &parser,
            ),
            RegexExpr::new(
                r#"(?u)\*\a\f\t\n\r\v\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#,
                RegexFormat::Raw(1),
                &parser.settings().regex_provider,
            )
            .unwrap(),
            ""
        );

        assert_json!(
            expr,
            r#"(?u)\*\a\f\t\n\r\v\x7F\x{10FFFF}\u007F\u{7F}\U0000007F\U{7F}"#
        );

        assert_err!(
            RegexExpr::lex_with("x", &FilterParser::new(&scheme)),
            LexErrorKind::ExpectedName("\" or r"),
            "x"
        );
    }
}
