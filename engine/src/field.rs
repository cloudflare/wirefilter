use lex::{expect, span, take_while, Lex, LexResult};

use std::fmt;

fn ident(input: &str) -> LexResult<&str> {
    take_while(input, "identifier character", |c| c.is_ascii_alphanumeric() || c == '_')
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Field<'a>(&'a str);

impl<'a> fmt::Debug for Field<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.path())
    }
}

impl<'a> Field<'a> {
    pub fn new(path: &'a str) -> Self {
        Field(path)
    }

    pub fn path(self) -> &'a str {
        self.0
    }
}

impl<'i> Lex<'i> for Field<'i> {
    fn lex(mut input: &'i str) -> LexResult<Self> {
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

    assert_ok!(Field::lex("is_tcp"), Field::new("is_tcp"), "");

    assert_err!(
        Field::lex("x..y"),
        LexErrorKind::ExpectedName("identifier character"),
        ".y"
    );

    assert_err!(
        Field::lex("x.#"),
        LexErrorKind::ExpectedName("identifier character"),
        "#"
    );
}
