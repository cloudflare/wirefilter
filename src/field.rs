use lex::{expect, span, take_while, Lex, LexResult};

use std::fmt;

fn ident(input: &str) -> LexResult<&str> {
    take_while(input, "alphanumeric character", char::is_alphanumeric)
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
    fn lex(mut input: &'a str) -> LexResult<'a, Self> {
        let initial_input = input;
        loop {
            input = ident(input)?.1;
            match expect(input, ".") {
                Ok(rest) => input = rest,
                Err(_) => break,
            };
        }
        Ok((Field::new(span(initial_input, input)), input))
    }
}

#[test]
fn test() {
    use lex::LexErrorKind;

    assert_ok!(Field::lex("x;"), Field::new("x"), ";");

    assert_ok!(Field::lex("x.y.z0-"), Field::new("x.y.z0"), "-");

    assert_err!(
        Field::lex("x..y"),
        LexErrorKind::CountMismatch("alphanumeric character", 0, 1),
        ".y"
    );

    assert_err!(
        Field::lex("x.#"),
        LexErrorKind::CountMismatch("alphanumeric character", 0, 1),
        "#"
    );
}
