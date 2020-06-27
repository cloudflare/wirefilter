use crate::lex::{expect, Lex, LexErrorKind, LexResult};
use serde::Serialize;
use std::str;

#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
pub struct ListName(Box<str>);

impl From<String> for ListName {
    fn from(src: String) -> Self {
        ListName(src.into_boxed_str())
    }
}

impl<'i> Lex<'i> for ListName {
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
}
