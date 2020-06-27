use std::str::FromStr;
use thiserror::Error;

#[derive(Debug, PartialEq, Error)]
pub enum Error {}

#[derive(Clone)]
pub struct Regex(String);

impl FromStr for Regex {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        Ok(Regex(s.to_owned()))
    }
}

impl Regex {
    pub fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}
