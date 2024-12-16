use crate::lex::{expect, Lex, LexErrorKind, LexResult};
use serde::Serialize;
use std::str;

#[derive(PartialEq, Eq, Clone, Serialize, Hash, Debug)]
pub struct ListName(Box<str>);

impl From<String> for ListName {
    fn from(src: String) -> Self {
        ListName(src.into_boxed_str())
    }
}

impl Lex<'_> for ListName {
    fn lex(input: &str) -> LexResult<'_, Self> {
        let mut res = String::new();
        let mut rest;
        let input = expect(input, "$")?;
        let mut iter = input.chars();
        loop {
            rest = iter.as_str();
            match iter.next() {
                Some(c) => match c {
                    'a'..='z' | '0'..='9' | '_' | '.' => res.push(c),
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

        if res.as_bytes().first() == Some(&b'.') || res.as_bytes().last() == Some(&b'.') {
            return Err((LexErrorKind::InvalidListName { name: res }, input));
        }

        Ok((res.into(), rest))
    }
}

impl ListName {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn valid() {
        assert_ok!(
            ListName::lex("$hello;"),
            ListName::from("hello".to_string()),
            ";"
        );

        assert_ok!(
            ListName::lex("$hello_world;"),
            ListName::from("hello_world".to_string()),
            ";"
        );

        assert_ok!(
            ListName::lex("$hello.world;"),
            ListName::from("hello.world".to_string()),
            ";"
        );

        assert_ok!(
            ListName::lex("$hello1234567890;"),
            ListName::from("hello1234567890".to_string()),
            ";"
        );

        assert_ok!(
            ListName::lex("$hello"),
            ListName::from("hello".to_string()),
            ""
        );
    }

    #[test]
    fn invalid_char() {
        assert_err!(
            ListName::lex("$;"),
            LexErrorKind::InvalidListName {
                name: ";".to_string(),
            },
            ";"
        );
    }

    #[test]
    fn eof_after_dollar() {
        assert_err!(
            ListName::lex("$"),
            LexErrorKind::InvalidListName {
                name: "".to_string(),
            },
            ""
        );
    }

    #[test]
    fn no_dollar() {
        assert_err!(
            ListName::lex("abc"),
            LexErrorKind::ExpectedLiteral("$"),
            "abc"
        );
    }

    #[test]
    fn special_char_at_start() {
        assert_err!(
            ListName::lex("$."),
            LexErrorKind::InvalidListName {
                name: ".".to_string(),
            },
            "."
        );

        assert_err!(
            ListName::lex("$.abc"),
            LexErrorKind::InvalidListName {
                name: ".abc".to_string(),
            },
            ".abc"
        );
    }

    #[test]
    fn special_char_at_end() {
        assert_err!(
            ListName::lex("$."),
            LexErrorKind::InvalidListName {
                name: ".".to_string(),
            },
            "."
        );

        assert_err!(
            ListName::lex("$abc."),
            LexErrorKind::InvalidListName {
                name: "abc.".to_string(),
            },
            "abc."
        );
    }
}
