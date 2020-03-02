use crate::lex::{expect, Lex, LexErrorKind, LexResult};
use serde::Serialize;
use std::str;

#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
pub struct List(Box<str>);

impl From<String> for List {
    fn from(src: String) -> Self {
        List(src.into_boxed_str())
    }
}

impl<'i> Lex<'i> for List {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let mut res = String::new();
        let mut rest;
        let mut iter;
        let input = expect(input, "$")?;
        iter = input.chars();
        loop {
            rest = iter.as_str();
            match iter.next() {
                Some(c) => match c {
                    'a'..='z' | '0'..='9' | '_' => res.push(c),
                    _ => {
                        if res.is_empty() {
                            return Err((
                                LexErrorKind::InvalidListName {
                                    name: c.to_string(),
                                },
                                input,
                            ));
                        } else {
                            break;
                        }
                    }
                },
                None => {
                    if res.is_empty() {
                        return Err((LexErrorKind::InvalidListName { name: res }, input));
                    } else {
                        break;
                    }
                }
            }
        }
        Ok((res.into(), rest))
    }
}

impl List {
    pub fn name(&self) -> &str {
        &self.0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn valid() {
        assert_ok!(List::lex("$hello;"), List::from("hello".to_string()), ";");

        assert_ok!(
            List::lex("$hello_world;"),
            List::from("hello_world".to_string()),
            ";"
        );

        assert_ok!(
            List::lex("$hello1234567890;"),
            List::from("hello1234567890".to_string()),
            ";"
        );

        assert_ok!(List::lex("$hello"), List::from("hello".to_string()), "");
    }

    #[test]
    fn invalid_char() {
        assert_err!(
            List::lex("$;"),
            LexErrorKind::InvalidListName {
                name: ";".to_string(),
            },
            ";"
        );
    }

    #[test]
    fn eof_after_dollar() {
        assert_err!(
            List::lex("$"),
            LexErrorKind::InvalidListName {
                name: "".to_string(),
            },
            ""
        );
    }

    #[test]
    fn no_dollar() {
        assert_err!(List::lex("abc"), LexErrorKind::ExpectedLiteral("$"), "abc");
    }
}
