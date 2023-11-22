use crate::{FilterParser, RegexFormat};
use std::borrow::Borrow;
use std::collections::HashSet;
use std::sync::{Arc, Mutex, OnceLock};

pub use regex::Error;

/// Wrapper around [`regex::bytes::Regex`]
#[derive(Clone)]
pub struct Regex {
    compiled_regex: Arc<regex::bytes::Regex>,
    format: RegexFormat,
}

fn get_regex_pool() -> &'static Mutex<HashSet<Regex>> {
    static REGEX_POOL: OnceLock<Mutex<HashSet<Regex>>> = OnceLock::new();
    REGEX_POOL.get_or_init(|| Mutex::new(HashSet::new()))
}

impl Drop for Regex {
    fn drop(&mut self) {
        // check whether this is the last strong reference to the regex, and
        // avoid deadlock by making sure to drop the last cached regex only
        // after we've dropped the lock on the pool.
        let cached_regex = if Arc::strong_count(&self.compiled_regex) == 2
            && Arc::weak_count(&self.compiled_regex) == 0
        {
            let mut pool = get_regex_pool().lock().unwrap();
            pool.take(self.as_str())
        } else {
            None
        };

        // now we can safely drop the regex, as there's no deadlock
        drop(cached_regex);
    }
}

impl Regex {
    /// Compiles a regular expression.
    pub fn new(
        pattern: &str,
        format: RegexFormat,
        parser: &FilterParser<'_>,
    ) -> Result<Self, Error> {
        let mut pool = get_regex_pool().lock().unwrap();
        if let Some(regex) = pool.get(pattern) {
            return Ok(regex.clone());
        }

        let compiled_regex = ::regex::bytes::RegexBuilder::new(pattern)
            .unicode(false)
            .size_limit(parser.regex_compiled_size_limit)
            .dfa_size_limit(parser.regex_dfa_size_limit)
            .build()?;

        let regex = Self {
            compiled_regex: Arc::from(compiled_regex),
            format,
        };

        pool.insert(regex.clone());
        Ok(regex)
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

impl Borrow<str> for Regex {
    fn borrow(&self) -> &str {
        self.compiled_regex.as_str()
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
