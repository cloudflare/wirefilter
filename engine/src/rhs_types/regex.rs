use lex::{expect, span, Lex, LexErrorKind, LexResult};
use std::fmt::{self, Debug, Formatter};

#[cfg(feature = "regex")]
pub type Error = ::regex::Error;

#[cfg(not(feature = "regex"))]
#[derive(Debug, PartialEq, Fail)]
pub enum Error {}

#[cfg(not(feature = "regex"))]
impl fmt::Display for Error {
    fn fmt(&self, _f: &mut Formatter) -> fmt::Result {
        match *self {}
    }
}

#[derive(Clone)]
pub struct Regex(
    #[cfg(feature = "regex")] ::regex::bytes::Regex,
    #[cfg(not(feature = "regex"))] String,
);

impl Regex {
    pub fn new(s: &str) -> Result<Self, Error> {
        Ok(Regex({
            #[cfg(feature = "regex")]
            {
                ::regex::bytes::RegexBuilder::new(s)
                    .unicode(false)
                    .build()?
            }

            #[cfg(not(feature = "regex"))]
            {
                s.to_owned()
            }
        }))
    }

    pub fn is_match(&self, text: &[u8]) -> bool {
        #[cfg(feature = "regex")]
        {
            self.0.is_match(text)
        }

        #[cfg(not(feature = "regex"))]
        {
            let _ = text;
            unimplemented!("Engine was built without regex support")
        }
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl PartialEq for Regex {
    fn eq(&self, other: &Regex) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for Regex {}

impl Debug for Regex {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

impl<'i> Lex<'i> for Regex {
    fn lex(input: &str) -> LexResult<Self> {
        let input = expect(input, "\"")?;
        let mut regex_buf = String::new();
        let mut in_char_class = false;
        let (regex_str, input) = {
            let mut iter = input.chars();
            loop {
                let before_char = iter.as_str();
                match iter
                    .next()
                    .ok_or_else(|| (LexErrorKind::MissingEndingQuote, input))?
                {
                    '\\' => {
                        if let Some(c) = iter.next() {
                            if in_char_class || c != '"' {
                                regex_buf.push('\\');
                            }
                            regex_buf.push(c);
                        }
                    }
                    '"' if !in_char_class => {
                        break (span(input, before_char), iter.as_str());
                    }
                    '[' if !in_char_class => {
                        in_char_class = true;
                        regex_buf.push('[');
                    }
                    ']' if in_char_class => {
                        in_char_class = false;
                        regex_buf.push(']');
                    }
                    c => {
                        regex_buf.push(c);
                    }
                };
            }
        };
        match Regex::new(&regex_buf) {
            Ok(regex) => Ok((regex, input)),
            Err(err) => Err((LexErrorKind::ParseRegex(err), regex_str)),
        }
    }
}

impl ::serde::Serialize for Regex {
    fn serialize<S: ::serde::Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.as_str().serialize(ser)
    }
}

#[test]
fn test() {
    let expr = assert_ok!(
        Regex::lex(r#""[a-z"\]]+\d{1,10}\"";"#),
        Regex::new(r#"[a-z"\]]+\d{1,10}""#).unwrap(),
        ";"
    );

    assert_eq!(
        ::serde_json::to_value(&expr).unwrap(),
        json!(r#"[a-z"\]]+\d{1,10}""#)
    );

    assert_err!(
        Regex::lex(r#""abcd\"#),
        LexErrorKind::MissingEndingQuote,
        "abcd\\"
    );
}
