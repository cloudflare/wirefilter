use crate::{
    ast::FilterAst,
    functions::Function,
    lex::{complete, expect, span, take_while, LexErrorKind, LexResult, LexWith},
    types::{GetType, Type},
};
use failure::Fail;
use fnv::FnvBuildHasher;
use indexmap::map::{Entry, IndexMap};
use serde::{Deserialize, Serialize, Serializer};
use std::{
    cmp::{max, min},
    error::Error,
    fmt::{self, Debug, Display, Formatter},
    ptr,
};



#[derive(PartialEq, Eq, Clone, Copy)]
pub(crate) struct Field<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl<'s> Serialize for Field<'s> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl<'s> Debug for Field<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for Field<'s> {
    fn lex_with(mut input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        let initial_input = input;

        loop {
            input = take_while(input, "identifier character", |c| {
                c.is_ascii_alphanumeric() || c == '_'
            })?
            .1;

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

impl<'s> Field<'s> {
    pub fn name(&self) -> &'s str {
        self.scheme.fields.get_index(self.index).unwrap().0
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn scheme(&self) -> &'s Scheme {
        self.scheme
    }
}

impl<'s> GetType for Field<'s> {
    fn get_type(&self) -> Type {
        *self.scheme.fields.get_index(self.index).unwrap().1
    }
}

/// An error that occurs if an unregistered field name was queried from a
/// [`Scheme`](struct@Scheme).
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "unknown field")]
pub struct UnknownFieldError;

/// An error that occurs if an unregistered function name was queried from a
/// [`Scheme`](struct@Scheme).
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "unknown function")]
pub struct UnknownFunctionError;

/// An error that occurs when previously defined field gets redefined.
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "attempt to redefine field {}", _0)]
pub struct FieldRedefinitionError(String);

/// An error that occurs when previously defined function gets redefined.
#[derive(Debug, PartialEq, Fail)]
#[fail(display = "attempt to redefine function {}", _0)]
pub struct FunctionRedefinitionError(String);

#[derive(Debug, PartialEq, Fail)]
pub enum ItemRedefinitionError {
    #[fail(display = "{}", _0)]
    Field(#[cause] FieldRedefinitionError),

    #[fail(display = "{}", _0)]
    Function(#[cause] FunctionRedefinitionError),
}

/// An opaque filter parsing error associated with the original input.
///
/// For now, you can just print it in a debug or a human-readable fashion.
#[derive(Debug, PartialEq)]
pub struct ParseError<'i> {
    kind: LexErrorKind,
    input: &'i str,
    line_number: usize,
    span_start: usize,
    span_len: usize,
}

impl<'i> Error for ParseError<'i> {}

impl<'i> ParseError<'i> {
    pub(crate) fn new(mut input: &'i str, (kind, span): (LexErrorKind, &'i str)) -> Self {
        let mut span_start = span.as_ptr() as usize - input.as_ptr() as usize;

        let (line_number, line_start) = input[..span_start]
            .match_indices('\n')
            .map(|(pos, _)| pos + 1)
            .scan(0, |line_number, line_start| {
                *line_number += 1;
                Some((*line_number, line_start))
            })
            .last()
            .unwrap_or_default();

        input = &input[line_start..];

        span_start -= line_start;
        let mut span_len = span.len();

        if let Some(line_end) = input.find('\n') {
            input = &input[..line_end];
            span_len = min(span_len, line_end - span_start);
        }

        ParseError {
            kind,
            input,
            line_number,
            span_start,
            span_len,
        }
    }
}

impl<'i> Display for ParseError<'i> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Filter parsing error ({}:{}):",
            self.line_number + 1,
            self.span_start + 1
        )?;

        writeln!(f, "{}", self.input)?;

        for _ in 0..self.span_start {
            write!(f, " ")?;
        }

        for _ in 0..max(1, self.span_len) {
            write!(f, "^")?;
        }

        writeln!(f, " {}", self.kind)?;

        Ok(())
    }
}

/// The main registry for fields and their associated types.
///
/// This is necessary to provide typechecking for runtime values provided
/// to the [execution context](::ExecutionContext) and also to aid parser
/// in ambiguous contexts.
#[derive(Default, Deserialize)]
#[serde(transparent)]
pub struct Scheme {
    fields: IndexMap<String, Type, FnvBuildHasher>,
    #[serde(skip)]
    functions: IndexMap<String, Function, FnvBuildHasher>,
}

impl PartialEq for Scheme {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl Eq for Scheme {}

impl<'s> Scheme {
    /// Creates a new scheme.
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates a new scheme with capacity for `n` fields.
    pub fn with_capacity(n: usize) -> Self {
        Scheme {
            fields: IndexMap::with_capacity_and_hasher(n, FnvBuildHasher::default()),
            functions: Default::default(),
        }
    }

    /// Registers a field and its corresponding type.
    pub fn add_field(&mut self, name: String, ty: Type) -> Result<(), ItemRedefinitionError> {
        if self.functions.contains_key(&name) {
            return Err(ItemRedefinitionError::Function(FunctionRedefinitionError(
                name,
            )));
        };
        match self.fields.entry(name) {
            Entry::Occupied(entry) => Err(ItemRedefinitionError::Field(FieldRedefinitionError(
                entry.key().to_string(),
            ))),
            Entry::Vacant(entry) => {
                entry.insert(ty);
                Ok(())
            }
        }
    }

    /// Registers a series of fields from an iterable, reporting any conflicts.
    pub fn try_from_iter(
        iter: impl IntoIterator<Item = (String, Type)>,
    ) -> Result<Self, ItemRedefinitionError> {
        let iter = iter.into_iter();
        let (low, _) = iter.size_hint();
        let mut scheme = Scheme::with_capacity(low);
        for (name, value) in iter {
            scheme.add_field(name, value)?;
        }
        Ok(scheme)
    }

    pub(crate) fn get_field_index(&'s self, name: &str) -> Result<Field<'s>, UnknownFieldError> {
        match self.fields.get_full(name) {
            Some((index, ..)) => Ok(Field {
                scheme: self,
                index,
            }),
            None => Err(UnknownFieldError),
        }
    }

    pub(crate) fn get_field_count(&self) -> usize {
        self.fields.len()
    }

    /// Registers a function
    pub fn add_function(
        &mut self,
        name: String,
        function: Function,
    ) -> Result<(), ItemRedefinitionError> {
        if self.fields.contains_key(&name) {
            return Err(ItemRedefinitionError::Field(FieldRedefinitionError(name)));
        };
        match self.functions.entry(name) {
            Entry::Occupied(entry) => Err(ItemRedefinitionError::Function(
                FunctionRedefinitionError(entry.key().to_string()),
            )),
            Entry::Vacant(entry) => {
                entry.insert(function);
                Ok(())
            }
        }
    }

    /// Registers a list of functions
    pub fn add_functions<I>(&mut self, functions: I) -> Result<(), ItemRedefinitionError>
    where
        I: IntoIterator<Item = (String, Function)>,
    {
        for (name, func) in functions {
            self.add_function(name, func)?;
        }
        Ok(())
    }

    pub(crate) fn get_function(&'s self, name: &str) -> Result<&'s Function, UnknownFunctionError> {
        self.functions.get(name).ok_or(UnknownFunctionError)
    }

    /// Parses a filter into an AST form.
    pub fn parse<'i>(&'s self, input: &'i str) -> Result<FilterAst<'s>, ParseError<'i>> {
        complete(FilterAst::lex_with(input.trim(), self)).map_err(|err| ParseError::new(input, err))
    }
}

/// A convenience macro for constructing a [`Scheme`](struct@Scheme) with static
/// contents.
#[macro_export]
macro_rules! Scheme {
    ($($ns:ident $(. $field:ident)*: $ty:ident),* $(,)*) => {
        $crate::Scheme::try_from_iter(
            [$(
                (
                    concat!(stringify!($ns) $(, ".", stringify!($field))*),
                    $crate::Type::$ty
                )
            ),*]
            .iter()
            .map(|&(k, v)| (k.to_owned(), v)),
        )
        // Treat duplciations in static schemes as a developer's mistake.
        .unwrap_or_else(|err| panic!("{}", err))
    };
}

#[test]
fn test_parse_error() {
    use indoc::indoc;

    let scheme = &Scheme! { num: Int };

    {
        let err = scheme.parse("xyz").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownField(UnknownFieldError),
                input: "xyz",
                line_number: 0,
                span_start: 0,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:1):
                xyz
                ^^^ unknown field
                "#
            )
        );
    }

    {
        let err = scheme.parse("xyz\n").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownField(UnknownFieldError),
                input: "xyz",
                line_number: 0,
                span_start: 0,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:1):
                xyz
                ^^^ unknown field
                "#
            )
        );
    }

    {
        let err = scheme.parse("\n\n    xyz").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownField(UnknownFieldError),
                input: "    xyz",
                line_number: 2,
                span_start: 4,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (3:5):
                    xyz
                    ^^^ unknown field
                "#
            )
        );
    }

    {
        let err = scheme
            .parse(indoc!(
                r#"
                num == 10 or
                num == true or
                num == 20
                "#
            ))
            .unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("digit"),
                input: "num == true or",
                line_number: 1,
                span_start: 7,
                span_len: 7
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (2:8):
                num == true or
                       ^^^^^^^ expected digit
                "#
            )
        );
    }
}

#[test]
fn test_field() {
    let scheme = &Scheme! {
        x: Bytes,
        x.y.z0: Int,
        is_TCP: Bool,
    };

    assert_ok!(
        Field::lex_with("x;", scheme),
        scheme.get_field_index("x").unwrap(),
        ";"
    );

    assert_ok!(
        Field::lex_with("x.y.z0-", scheme),
        scheme.get_field_index("x.y.z0").unwrap(),
        "-"
    );

    assert_ok!(
        Field::lex_with("is_TCP", scheme),
        scheme.get_field_index("is_TCP").unwrap(),
        ""
    );

    assert_err!(
        Field::lex_with("x..y", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        ".y"
    );

    assert_err!(
        Field::lex_with("x.#", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        "#"
    );

    assert_err!(
        Field::lex_with("x.y.z;", scheme),
        LexErrorKind::UnknownField(UnknownFieldError),
        "x.y.z"
    );
}

#[test]
#[should_panic(expected = "attempt to redefine field foo")]
fn test_static_field_type_override() {
    Scheme! { foo: Int, foo: Int };
}

#[test]
fn test_field_type_override() {
    let mut scheme = Scheme! { foo: Int };

    assert_eq!(
        scheme.add_field("foo".into(), Type::Bytes).unwrap_err(),
        ItemRedefinitionError::Field(FieldRedefinitionError("foo".into()))
    )
}
