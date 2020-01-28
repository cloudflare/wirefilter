use failure::Fail;
use std::fmt;
use std::str::FromStr;

#[derive(Debug, PartialEq, Fail)]
pub enum Error {}

impl fmt::Display for Error {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

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
