use super::{FilterAst, FilterValueAst};
use crate::{
    RegexProvider,
    lex::{LexErrorKind, LexResult, LexWith, complete},
    rhs_types::RegexDefaultProvider,
    scheme::Scheme,
};
use std::cmp::{max, min};
use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};
use std::sync::{Arc, LazyLock};

/// An opaque filter parsing error associated with the original input.
///
/// For now, you can just print it in a debug or a human-readable fashion.
#[derive(Debug, PartialEq)]
pub struct ParseError<'i> {
    /// The error that occurred when parsing the input
    pub(crate) kind: LexErrorKind,

    /// The input that caused the parse error
    pub(crate) input: &'i str,

    /// The line number on the input where the error occurred
    pub(crate) line_number: usize,

    /// The start of the bad input
    pub(crate) span_start: usize,

    /// The number of characters that span the bad input
    pub(crate) span_len: usize,
}

impl Error for ParseError<'_> {}

impl<'i> ParseError<'i> {
    /// Create a new ParseError for the input, LexErrorKind and span in the
    /// input.
    pub fn new(mut input: &'i str, (kind, span): (LexErrorKind, &'i str)) -> Self {
        let input_range = input.as_ptr() as usize..=input.as_ptr() as usize + input.len();
        assert!(
            input_range.contains(&(span.as_ptr() as usize))
                && input_range.contains(&(span.as_ptr() as usize + span.len()))
        );
        let mut span_start = span.as_ptr() as usize - input.as_ptr() as usize;

        let (line_number, line_start) = input[..span_start]
            .match_indices('\n')
            .map(|(pos, _)| pos + 1)
            .scan(0, |line_number, line_start| {
                *line_number += 1;
                Some((*line_number, line_start))
            })
            .last()
            .unwrap_or_default();

        input = &input[line_start..];

        span_start -= line_start;
        let mut span_len = span.len();

        if let Some(line_end) = input.find('\n') {
            input = &input[..line_end];
            span_len = min(span_len, line_end - span_start);
        }

        ParseError {
            kind,
            input,
            line_number,
            span_start,
            span_len,
        }
    }
}

impl Display for ParseError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Filter parsing error ({}:{}):",
            self.line_number + 1,
            self.span_start + 1
        )?;

        writeln!(f, "{}", self.input)?;

        for _ in 0..self.span_start {
            write!(f, " ")?;
        }

        for _ in 0..max(1, self.span_len) {
            write!(f, "^")?;
        }

        writeln!(f, " {}", self.kind)?;

        Ok(())
    }
}

static DEFAULT_REGEX_PROVIDER: LazyLock<Arc<dyn RegexProvider>> =
    LazyLock::new(|| Arc::new(RegexDefaultProvider::default()));

/// Parser settings.
#[derive(Clone, Debug)]
pub struct ParserSettings {
    /// Regex provider.
    pub regex_provider: Arc<dyn RegexProvider>,
    /// Maximum number of star metacharacters allowed in a wildcard.
    /// Default: unlimited
    pub wildcard_star_limit: usize,
}

impl PartialEq for ParserSettings {
    fn eq(&self, other: &Self) -> bool {
        let Self {
            regex_provider,
            wildcard_star_limit,
        } = self;
        Arc::ptr_eq(regex_provider, &other.regex_provider)
            && *wildcard_star_limit == other.wildcard_star_limit
    }
}

impl Eq for ParserSettings {}

impl Default for ParserSettings {
    #[inline]
    fn default() -> Self {
        Self {
            regex_provider: DEFAULT_REGEX_PROVIDER.clone(),
            wildcard_star_limit: usize::MAX,
        }
    }
}

/// A structure used to drive parsing of an expression into a [`FilterAst`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilterParser<'s> {
    pub(crate) scheme: &'s Scheme,
    pub(crate) settings: ParserSettings,
}

impl<'s> FilterParser<'s> {
    /// Creates a new parser with default settings.
    #[inline]
    pub fn new(scheme: &'s Scheme) -> Self {
        Self {
            scheme,
            settings: ParserSettings::default(),
        }
    }

    /// Creates a new parser with the specified settings.
    #[inline]
    pub fn with_settings(scheme: &'s Scheme, settings: ParserSettings) -> Self {
        Self { scheme, settings }
    }

    /// Returns the [`Scheme`](struct@Scheme) for which this parser has been constructor for.
    #[inline]
    pub fn scheme(&self) -> &'s Scheme {
        self.scheme
    }

    #[inline]
    pub(crate) fn lex_as<'i, L: for<'p> LexWith<'i, &'p FilterParser<'s>>>(
        &self,
        input: &'i str,
    ) -> LexResult<'i, L> {
        L::lex_with(input, self)
    }

    /// Parses a filter expression into an AST form.
    pub fn parse<'i>(&self, input: &'i str) -> Result<FilterAst, ParseError<'i>> {
        complete(self.lex_as(input.trim())).map_err(|err| ParseError::new(input, err))
    }

    /// Parses a value expression into an AST form.
    pub fn parse_value<'i>(&self, input: &'i str) -> Result<FilterValueAst, ParseError<'i>> {
        complete(self.lex_as(input.trim())).map_err(|err| ParseError::new(input, err))
    }

    /// Retrieve parser settings.
    #[inline]
    pub fn settings(&self) -> &ParserSettings {
        &self.settings
    }

    /// Set the maximum number of star metacharacters allowed in a wildcard.
    #[inline]
    pub fn wildcard_set_star_limit(&mut self, wildcard_star_limit: usize) {
        self.settings.wildcard_star_limit = wildcard_star_limit;
    }

    /// Get the maximum number of star metacharacters allowed in a wildcard.
    #[inline]
    pub fn wildcard_get_star_limit(&self) -> usize {
        self.settings.wildcard_star_limit
    }
}
