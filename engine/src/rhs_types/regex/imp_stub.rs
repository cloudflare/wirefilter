use std::fmt;

#[derive(Clone)]
pub struct Regex(String);

#[derive(Debug, PartialEq, Fail)]
pub enum Error {}

impl fmt::Display for Error {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {}
    }
}

impl Regex {
    pub fn new(s: &str) -> Result<Self, Error> {
        Ok(Regex(s.to_owned()))
    }

    pub fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}
