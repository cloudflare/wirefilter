use std::str::FromStr;
use thiserror::Error;

/// Dummy regex error.
#[derive(Debug, PartialEq, Error)]
pub enum Error {}

/// Dummy regex wrapper that can only store a pattern
/// but not actually be used for matching.
#[derive(Clone)]
pub struct Regex(String);

impl FromStr for Regex {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        Ok(Regex(s.to_owned()))
    }
}

impl Regex {
    /// Not implemented and will panic if called.
    pub fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }

    /// Returns the original string of this dummy regex wrapper.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}
