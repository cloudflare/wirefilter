use ast::Filter;
use fnv::FnvBuildHasher;
use indexmap::map::{Entry, IndexMap};
use lex::{complete, expect, span, take_while, LexError, LexErrorKind, LexResult};
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

impl<'s> FieldIndex<'s> {
    pub fn name(&self) -> &'s str {
        self.scheme.fields.get_index(self.index).unwrap().0
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn lex<'i>(scheme: &'s Scheme, mut input: &'i str) -> LexResult<'i, Self> {
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
            .ok_or_else(|| (LexErrorKind::UnknownField, name))?;

        Ok((field, input))
    }
}

impl<'s> GetType for FieldIndex<'s> {
    fn get_type(&self) -> Type {
        *self.scheme.fields.get_index(self.index).unwrap().1
    }
}

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

    pub fn get_field_entry(&'s self, name: &str) -> Option<(FieldIndex<'s>, Type)> {
        self.fields.get_full(name).map(|(index, _, ty)| {
            (
                FieldIndex {
                    scheme: self,
                    index,
                },
                *ty,
            )
        })
    }

    pub fn get_field_index(&'s self, name: &str) -> Option<FieldIndex<'s>> {
        self.get_field_entry(name).map(|(field, _)| field)
    }

    pub fn get_field_count(&self) -> usize {
        self.fields.len()
    }

    pub fn parse<'i>(&'s self, input: &'i str) -> Result<Filter<'s>, LexError<'i>> {
        complete(Filter::lex(self, input))
    }
}

#[test]
fn test_field() {
    let scheme: Scheme = [
        ("x", Type::Bytes),
        ("x.y.z0", Type::Unsigned),
        ("is_TCP", Type::Bool),
    ].iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect();

    assert_ok!(
        FieldIndex::lex(&scheme, "x;"),
        scheme.get_field_index("x").unwrap(),
        ";"
    );

    assert_ok!(
        FieldIndex::lex(&scheme, "x.y.z0-"),
        scheme.get_field_index("x.y.z0").unwrap(),
        "-"
    );

    assert_ok!(
        FieldIndex::lex(&scheme, "is_TCP"),
        scheme.get_field_index("is_TCP").unwrap(),
        ""
    );

    assert_err!(
        FieldIndex::lex(&scheme, "x..y"),
        LexErrorKind::ExpectedName("identifier character"),
        ".y"
    );

    assert_err!(
        FieldIndex::lex(&scheme, "x.#"),
        LexErrorKind::ExpectedName("identifier character"),
        "#"
    );

    assert_err!(
        FieldIndex::lex(&scheme, "x.y.z;"),
        LexErrorKind::UnknownField,
        "x.y.z"
    );
}
