use lex::{expect, span, Lex, LexErrorKind, LexResult};
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use serde::de::Error as DeError;

use std::borrow::Cow;
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::str::FromStr;

pub struct Regex(::regex::bytes::Regex);

impl Regex {
    pub fn new(s: &str) -> Result<Self, ::regex::Error> {
        Self::from_str(s)
    }

    pub fn is_match(&self, text: &[u8]) -> bool {
        self.0.is_match(text)
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl FromStr for Regex {
    type Err = ::regex::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        ::regex::bytes::RegexBuilder::new(s).unicode(false).build().map(Regex)
    }
}

impl PartialEq for Regex {
    fn eq(&self, other: &Regex) -> bool {
        self.0.as_str() == other.0.as_str()
    }
}

impl Eq for Regex {}

impl Hash for Regex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.as_str().hash(state)
    }
}

impl Debug for Regex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Serialize for Regex {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.as_str().serialize(ser)
    }
}

impl<'de> Deserialize<'de> for Regex {
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Regex, D::Error> {
        let src = <Cow<str>>::deserialize(de)?;
        Regex::new(&src).map_err(D::Error::custom)
    }
}

impl<'i> Lex<'i> for Regex {
    fn lex(input: &str) -> LexResult<Self> {
        let input = expect(input, "\"")?;
        let (regex_str, input) = {
            let mut iter = input.chars();
            loop {
                let before_char = iter.as_str();
                match iter.next()
                    .ok_or_else(|| (LexErrorKind::MissingEndingQuote, input))?
                {
                    '\\' => {
                        iter.next();
                    }
                    '"' => {
                        break (span(input, before_char), iter.as_str());
                    }
                    _ => {}
                };
            }
        };
        match regex_str.parse() {
            Ok(regex) => Ok((regex, input)),
            Err(err) => Err((LexErrorKind::ParseRegex(err), regex_str)),
        }
    }
}
