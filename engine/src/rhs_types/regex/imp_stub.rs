use thiserror::Error;

use crate::{FilterParser, RegexFormat};

/// Dummy regex error.
#[derive(Debug, PartialEq, Error)]
pub enum Error {}

/// Dummy regex wrapper that can only store a pattern
/// but not actually be used for matching.
#[derive(Clone)]
pub struct Regex {
    pattern: String,
    format: RegexFormat,
}

impl Regex {
    /// Creates a new dummy regex.
    pub fn new(pattern: &str, format: RegexFormat, _: &FilterParser<'_>) -> Result<Self, Error> {
        Ok(Self {
            pattern: pattern.to_string(),
            format,
        })
    }

    /// Not implemented and will panic if called.
    pub fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }

    /// Returns the original string of this dummy regex wrapper.
    pub fn as_str(&self) -> &str {
        self.pattern.as_str()
    }

    /// Returns the format behind the regex
    pub fn format(&self) -> RegexFormat {
        self.format
    }
}
