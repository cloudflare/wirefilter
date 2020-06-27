use crate::{FilterParser, RegexFormat};

pub use regex::Error;

/// Wrapper around [`regex::bytes::Regex`]
#[derive(Clone)]
pub struct Regex {
    compiled_regex: regex::bytes::Regex,
    format: RegexFormat,
}

impl Regex {
    /// Compiles a regular expression.
    pub fn new(
        pattern: &str,
        format: RegexFormat,
        parser: &FilterParser<'_>,
    ) -> Result<Self, Error> {
        ::regex::bytes::RegexBuilder::new(pattern)
            .unicode(false)
            .size_limit(parser.regex_compiled_size_limit)
            .dfa_size_limit(parser.regex_dfa_size_limit)
            .build()
            .map(|r| Regex {
                compiled_regex: r,
                format,
            })
    }

    /// Returns true if and only if the regex matches the string given.
    pub fn is_match(&self, text: &[u8]) -> bool {
        self.compiled_regex.is_match(text)
    }

    /// Returns the original string of this regex.
    pub fn as_str(&self) -> &str {
        self.compiled_regex.as_str()
    }

    /// Returns the format behind the regex
    pub fn format(&self) -> RegexFormat {
        self.format
    }
}

impl From<Regex> for regex::bytes::Regex {
    fn from(regex: Regex) -> Self {
        regex.compiled_regex
    }
}

#[test]
fn test_compiled_size_limit() {
    use crate::Scheme;

    let scheme = Scheme::default();

    const COMPILED_SIZE_LIMIT: usize = 1024 * 1024;
    let mut parser = FilterParser::new(&scheme);
    parser.regex_set_compiled_size_limit(COMPILED_SIZE_LIMIT);
    assert_eq!(
        Regex::new(".{4079,65535}", RegexFormat::Literal, &parser),
        Err(Error::CompiledTooBig(COMPILED_SIZE_LIMIT))
    );
}
