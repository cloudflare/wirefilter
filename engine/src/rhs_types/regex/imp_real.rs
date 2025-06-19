use super::Error;
use crate::{RegexFormat, RegexProvider};
use std::ops::Deref;
use std::sync::Arc;

/// Wrapper around [`regex_automata::meta::Regex`]
#[derive(Clone)]
pub struct Regex {
    pattern: Arc<str>,
    regex: regex_automata::meta::Regex,
    format: RegexFormat,
}

impl Regex {
    /// Compiles a regular expression.
    pub fn new(
        pattern: &str,
        format: RegexFormat,
        provider: &impl RegexProvider,
    ) -> Result<Self, Error> {
        provider.lookup(pattern).map(|regex| Regex {
            pattern: Arc::from(pattern),
            regex,
            format,
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
}

impl From<Regex> for regex_automata::meta::Regex {
    #[inline]
    fn from(regex: Regex) -> Self {
        regex.regex
    }
}

impl Deref for Regex {
    type Target = regex_automata::meta::Regex;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.regex
    }
}

#[test]
fn test_compiled_size_limit() {
    use super::{DefaultRegexProvider, RegexSettings};

    const COMPILED_SIZE_LIMIT: usize = 1024 * 1024;
    let settings = RegexSettings {
        compiled_size_limit: COMPILED_SIZE_LIMIT,
        ..Default::default()
    };
    let regex_provider = DefaultRegexProvider::new(settings);
    assert_eq!(
        Regex::new(".{4079,65535}", RegexFormat::Literal, &regex_provider),
        Err(Error::CompiledTooBig(COMPILED_SIZE_LIMIT))
    );
}
