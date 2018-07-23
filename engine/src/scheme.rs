use ast::Filter;
use fnv::FnvBuildHasher;
use indexmap::map::{Entry, IndexMap};
use lex::{complete, expect, span, take_while, LexError, LexErrorKind, LexResult, LexWith};
use std::{
    fmt,
    hash::{Hash, Hasher},
    iter::FromIterator,
    ptr,
};
use types::{GetType, Type};

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct FieldIndex<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl<'s> fmt::Debug for FieldIndex<'s> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<'s> Hash for FieldIndex<'s> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.name().hash(h)
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FieldIndex<'s> {
    fn lex(mut input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        loop {
            input = take_while(input, "identifier character", |c| {
                c.is_ascii_alphanumeric() || c == '_'
            })?.1;

            match expect(input, ".") {
                Ok(rest) => input = rest,
                Err(_) => break,
            };
        }

        let name = span(initial_input, input);

        let field = scheme
            .get_field_index(name)
            .map_err(|err| (LexErrorKind::UnknownField(err), name))?;

        Ok((field, input))
    }
}

impl<'s> FieldIndex<'s> {
    pub fn name(&self) -> &'s str {
        self.scheme.fields.get_index(self.index).unwrap().0
    }

    pub fn index(&self) -> usize {
        self.index
    }
}

impl<'s> GetType for FieldIndex<'s> {
    fn get_type(&self) -> Type {
        *self.scheme.fields.get_index(self.index).unwrap().1
    }
}

#[derive(Debug, PartialEq, Fail)]
#[fail(display = "unknown field")]
pub struct UnknownFieldError;

#[derive(Default)]
pub struct Scheme {
    fields: IndexMap<String, Type, FnvBuildHasher>,
}

impl FromIterator<(String, Type)> for Scheme {
    fn from_iter<I: IntoIterator<Item = (String, Type)>>(iter: I) -> Self {
        Scheme {
            fields: IndexMap::from_iter(iter),
        }
    }
}

impl PartialEq for Scheme {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl Eq for Scheme {}

impl<'s> Scheme {
    pub fn add_field(&mut self, name: String, ty: Type) {
        match self.fields.entry(name) {
            Entry::Occupied(entry) => {
                panic!("Tried to register field {} with type {:?} but it's already registered with type {:?}", entry.key(), ty, entry.get())
            }
            Entry::Vacant(entry) => {
                entry.insert(ty);
            }
        }
    }

    pub fn get_field_name(&'s self, index: usize) -> Result<&'s str, UnknownFieldError> {
        match self.fields.get_index(index) {
            Some((name, ..)) => Ok(name),
            _ => Err(UnknownFieldError),
        }
    }

    pub fn get_field_index(&'s self, name: &str) -> Result<FieldIndex<'s>, UnknownFieldError> {
        match self.fields.get_full(name) {
            Some((index, ..)) => Ok(FieldIndex {
                scheme: self,
                index,
            }),
            None => Err(UnknownFieldError),
        }
    }

    pub fn get_field_count(&self) -> usize {
        self.fields.len()
    }

    pub fn parse<'i>(&'s self, input: &'i str) -> Result<Filter<'s>, LexError<'i>> {
        complete(Filter::lex(input, self))
    }
}

#[test]
fn test_field() {
    let scheme = &[
        ("x", Type::Bytes),
        ("x.y.z0", Type::Unsigned),
        ("is_TCP", Type::Bool),
    ].iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    assert_ok!(
        FieldIndex::lex("x;", scheme),
        scheme.get_field_index("x").unwrap(),
        ";"
    );

    assert_ok!(
        FieldIndex::lex("x.y.z0-", scheme),
        scheme.get_field_index("x.y.z0").unwrap(),
        "-"
    );

    assert_ok!(
        FieldIndex::lex("is_TCP", scheme),
        scheme.get_field_index("is_TCP").unwrap(),
        ""
    );

    assert_err!(
        FieldIndex::lex("x..y", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        ".y"
    );

    assert_err!(
        FieldIndex::lex("x.#", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        "#"
    );

    assert_err!(
        FieldIndex::lex("x.y.z;", scheme),
        LexErrorKind::UnknownField(UnknownFieldError),
        "x.y.z"
    );
}
