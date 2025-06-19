use super::{Error, Regex};
use crate::RegexProvider;
use std::sync::Arc;

pub(crate) type MetaRegex = regex_automata::meta::Regex;

impl Regex for MetaRegex {
    #[inline]
    fn is_match(&self, input: &[u8]) -> bool {
        MetaRegex::is_match(self, input)
    }
}

/// Regex settings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RegexSettings {
    /// Approximate size of the cache used by the DFA of a regex.
    /// Default: 10MB
    pub dfa_size_limit: usize,
    /// Approximate size limit of the compiled regular expression.
    /// Default: 2MB
    pub compiled_size_limit: usize,
}

impl Default for RegexSettings {
    #[inline]
    fn default() -> Self {
        Self {
            // Default value extracted from the regex crate.
            compiled_size_limit: 10 * (1 << 20),
            // Default value extracted from the regex crate.
            dfa_size_limit: 2 * (1 << 20),
        }
    }
}

/// Default regex provider.
#[derive(Debug, Default)]
pub struct RegexDefaultProvider {
    settings: RegexSettings,
}

impl RegexDefaultProvider {
    /// Creates a new default regex provider.
    pub const fn new(settings: RegexSettings) -> Self {
        Self { settings }
    }

    /// Retrieves the syntax configuration that will be used to build the regex.
    #[inline]
    pub fn syntax_config() -> regex_automata::util::syntax::Config {
        regex_automata::util::syntax::Config::new()
            .unicode(false)
            .utf8(false)
    }

    /// Retrieves the meta configuration that will be used to build the regex.
    #[inline]
    pub fn meta_config(settings: &RegexSettings) -> regex_automata::meta::Config {
        regex_automata::meta::Config::new()
            .match_kind(regex_automata::MatchKind::LeftmostFirst)
            .utf8_empty(false)
            .dfa(false)
            .nfa_size_limit(Some(settings.compiled_size_limit))
            .onepass_size_limit(Some(settings.compiled_size_limit))
            .dfa_size_limit(Some(settings.compiled_size_limit))
            .hybrid_cache_capacity(settings.dfa_size_limit)
    }

    /// Builds a new regex object from the provided pattern.
    pub fn build(&self, pattern: &str) -> Result<MetaRegex, Error> {
        ::regex_automata::meta::Builder::new()
            .configure(Self::meta_config(&self.settings))
            .syntax(Self::syntax_config())
            .build(pattern)
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
}

impl RegexProvider for RegexDefaultProvider {
    fn lookup_regex(&self, pattern: &str) -> Result<Arc<dyn Regex>, Error> {
        self.build(pattern).map(|re| Arc::new(re) as Arc<dyn Regex>)
    }
}

#[test]
fn test_compiled_size_limit() {
    use super::{RegexDefaultProvider, RegexSettings};
    use crate::{RegexExpr, RegexFormat};

    const COMPILED_SIZE_LIMIT: usize = 1024 * 1024;
    let settings = RegexSettings {
        compiled_size_limit: COMPILED_SIZE_LIMIT,
        ..Default::default()
    };
    let regex_provider = RegexDefaultProvider::new(settings);
    assert_eq!(
        RegexExpr::new(".{4079,65535}", RegexFormat::Literal, &regex_provider),
        Err(Error::CompiledTooBig(COMPILED_SIZE_LIMIT))
    );
}
