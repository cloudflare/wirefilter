use {Lex, LexResult};
use utils::{expect, list, take_while};

use std::fmt;

fn ident(input: &str) -> LexResult<&str> {
    take_while(input, "alphabetic", char::is_alphabetic)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Field<'a> {
    pub path: &'a str,
}

impl<'a> fmt::Debug for Field<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.path)
    }
}

impl<'a> Field<'a> {
    pub fn new(path: &'a str) -> Self {
        Field { path }
    }
}

impl<'a> Lex<'a> for Field<'a> {
    fn lex(input: &'a str) -> LexResult<'a, Self> {
        let (path, rest) = list(input, |input| expect(input, "."), ident)?;
        Ok((Field::new(path), rest))
    }
}
