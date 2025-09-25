use regex_automata::MatchKind;

use super::Error;
use crate::{ParserSettings, RegexFormat};
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
    /// Retrieves the syntax configuration that will be used to build the regex.
    #[inline]
    fn syntax_config() -> regex_automata::util::syntax::Config {
        regex_automata::util::syntax::Config::new()
            .unicode(false)
            .utf8(false)
    }

    /// Retrieves the meta configuration that will be used to build the regex.
    #[inline]
    fn meta_config(settings: &ParserSettings) -> regex_automata::meta::Config {
        regex_automata::meta::Config::new()
            .match_kind(MatchKind::LeftmostFirst)
            .utf8_empty(false)
            .dfa(false)
            .nfa_size_limit(Some(settings.regex_compiled_size_limit))
            .onepass(false)
            .dfa_size_limit(Some(settings.regex_compiled_size_limit))
            .hybrid_cache_capacity(settings.regex_dfa_size_limit)
    }

    /// Compiles a regular expression.
    pub fn new(
        pattern: &str,
        format: RegexFormat,
        settings: &ParserSettings,
    ) -> Result<Self, Error> {
        ::regex_automata::meta::Builder::new()
            .configure(Self::meta_config(settings))
            .syntax(Self::syntax_config())
            .build(pattern)
            .map(|regex| Regex {
                pattern: Arc::from(pattern),
                regex,
                format,
            })
            .map_err(|err| {
                if let Some(limit) = err.size_limit() {
                    Error::CompiledTooBig(limit)
                } else if let Some(syntax) = err.syntax_error() {
                    Error::Syntax(syntax.to_string())
                } else {
                    Error::Other(err.to_string())
                }
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
    const COMPILED_SIZE_LIMIT: usize = 1024 * 1024;
    let settings = ParserSettings {
        regex_compiled_size_limit: COMPILED_SIZE_LIMIT,
        ..Default::default()
    };
    assert_eq!(
        Regex::new(".{4079,65535}", RegexFormat::Literal, &settings),
        Err(Error::CompiledTooBig(COMPILED_SIZE_LIMIT))
    );
}
