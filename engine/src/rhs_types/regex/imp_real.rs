use std::str::FromStr;

pub use regex::Error;

/// Wrapper around [`regex::bytes::Regex`]
#[derive(Clone)]
pub struct Regex(regex::bytes::Regex);

impl FromStr for Regex {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        ::regex::bytes::RegexBuilder::new(s)
            .unicode(false)
            .build()
            .map(Regex)
    }
}

impl Regex {
    /// Returns true if and only if the regex matches the string given.
    pub fn is_match(&self, text: &[u8]) -> bool {
        self.0.is_match(text)
    }

    /// Returns the original string of this regex.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}
