use crate::{
    ast::parse::{FilterParser, ParseError},
    ast::{FilterAst, FilterValueAst},
    functions::FunctionDefinition,
    lex::{expect, span, take_while, Lex, LexErrorKind, LexResult, LexWith},
    list_matcher::ListDefinition,
    types::{GetType, RhsValue, Type},
};
use fnv::FnvBuildHasher;
use serde::ser::SerializeMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::hash_map::Entry;
use std::sync::Arc;
use std::{
    collections::HashMap,
    convert::TryFrom,
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
    iter::Iterator,
    ptr,
};
use thiserror::Error;

/// An error that occurs if two underlying [schemes](struct@Scheme)
/// don't match.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("underlying schemes do not match")]
pub struct SchemeMismatchError;

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize)]
#[serde(tag = "kind", content = "value")]
/// FieldIndex is an enum with variants [`ArrayIndex(usize)`],
/// representing an index into an Array, or `[MapKey(String)`],
/// representing a key into a Map.
///
/// ```
/// #[allow(dead_code)]
/// enum FieldIndex {
///     ArrayIndex(u32),
///     MapKey(String),
/// }
/// ```
pub enum FieldIndex {
    /// Index into an Array
    ArrayIndex(u32),

    /// Key into a Map
    MapKey(String),

    /// Map each element by applying a function or a comparison
    MapEach,
}

impl<'i> Lex<'i> for FieldIndex {
    fn lex(input: &'i str) -> LexResult<'i, Self> {
        if let Ok(input) = expect(input, "*") {
            return Ok((FieldIndex::MapEach, input));
        }

        // The token inside an [] can be either an integer index into an Array
        // or a string key into a Map. The token is a key into a Map if it
        // starts and ends with "\"", otherwise an integer index or an error.
        let (rhs, rest) = match expect(input, "\"") {
            Ok(_) => RhsValue::lex_with(input, Type::Bytes),
            Err(_) => RhsValue::lex_with(input, Type::Int).map_err(|_| {
                (
                    LexErrorKind::ExpectedLiteral(
                        "expected quoted utf8 string or positive integer",
                    ),
                    input,
                )
            }),
        }?;

        match rhs {
            RhsValue::Int(i) => match u32::try_from(i) {
                Ok(u) => Ok((FieldIndex::ArrayIndex(u), rest)),
                Err(_) => Err((
                    LexErrorKind::ExpectedLiteral("expected positive integer as index"),
                    input,
                )),
            },
            RhsValue::Bytes(b) => match String::from_utf8(b.to_vec()) {
                Ok(s) => Ok((FieldIndex::MapKey(s), rest)),
                Err(_) => Err((LexErrorKind::ExpectedLiteral("expected utf8 string"), input)),
            },
            _ => unreachable!(),
        }
    }
}

/// An error when an index is invalid for a type.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("cannot access index {index:?} for type {actual:?}")]
pub struct IndexAccessError {
    /// Index that could not be accessed.
    pub index: FieldIndex,
    /// Provided value type.
    pub actual: Type,
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
/// A structure to represent a field inside a [`Scheme`](struct@Scheme).
pub struct Field<'s> {
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
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        match Identifier::lex_with(input, scheme) {
            Ok((Identifier::Field(f), rest)) => Ok((f, rest)),
            Ok((Identifier::Function(_), rest)) => Err((
                LexErrorKind::UnknownField(UnknownFieldError),
                span(input, rest),
            )),
            Err((LexErrorKind::UnknownIdentifier, s)) => {
                Err((LexErrorKind::UnknownField(UnknownFieldError), s))
            }
            Err(err) => Err(err),
        }
    }
}

impl<'s> Field<'s> {
    /// Returns the field's name as recorded in the [`Scheme`](struct@Scheme).
    #[inline]
    pub fn name(&self) -> &'s str {
        &self.scheme.fields[self.index].0
    }

    /// Get the field's index in the [`Scheme`](struct@Scheme) identifier's list.
    #[inline]
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the [`Scheme`](struct@Scheme) to which this field belongs to.
    #[inline]
    pub fn scheme(&self) -> &'s Scheme {
        self.scheme
    }
}

impl<'s> GetType for Field<'s> {
    #[inline]
    fn get_type(&self) -> Type {
        self.scheme.fields[self.index].1
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
/// A structure to represent a function inside a [`Scheme`](struct@Scheme).
pub struct Function<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl<'s> Serialize for Function<'s> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl<'s> Debug for Function<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for Function<'s> {
    fn lex_with(input: &'i str, scheme: &'s Scheme) -> LexResult<'i, Self> {
        match Identifier::lex_with(input, scheme) {
            Ok((Identifier::Function(f), rest)) => Ok((f, rest)),
            Ok((Identifier::Field(_), rest)) => Err((
                LexErrorKind::UnknownFunction(UnknownFunctionError),
                span(input, rest),
            )),
            Err((LexErrorKind::UnknownIdentifier, s)) => {
                Err((LexErrorKind::UnknownFunction(UnknownFunctionError), s))
            }
            Err(err) => Err(err),
        }
    }
}

impl<'s> Function<'s> {
    /// Returns the function's name as recorded in the [`Scheme`](struct@Scheme).
    #[inline]
    pub fn name(&self) -> &'s str {
        &self.scheme.functions[self.index].0
    }

    /// Get the function's index in the [`Scheme`](struct@Scheme) identifier's list.
    #[inline]
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the [`Scheme`](struct@Scheme) to which this function belongs to.
    #[inline]
    pub fn scheme(&self) -> &'s Scheme {
        self.scheme
    }

    #[inline]
    pub(crate) fn as_definition(&self) -> &'s dyn FunctionDefinition {
        &*self.scheme.functions[self.index].1
    }
}

/// An enum to represent an entry inside a [`Scheme`](struct@Scheme).
/// It can be either a [`Field`](struct@Field) or a [`Function`](struct@Function).
#[derive(Debug)]
pub enum Identifier<'s> {
    /// Identifier is a [`Field`](struct@Field)
    Field(Field<'s>),
    /// Identifier is a [`Function`](struct@Function)
    Function(Function<'s>),
}

impl<'s> Identifier<'s> {
    /// Converts the identifier into a [`Field`](struct@Field) if possible.
    pub fn into_field(self) -> Option<Field<'s>> {
        match self {
            Self::Field(f) => Some(f),
            _ => None,
        }
    }

    /// Converts the identifier into a [`Function`](struct@Function) if possible.
    pub fn into_function(self) -> Option<Function<'s>> {
        match self {
            Self::Function(f) => Some(f),
            _ => None,
        }
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for Identifier<'s> {
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
            .get(name)
            .ok_or((LexErrorKind::UnknownIdentifier, name))?;

        Ok((field, input))
    }
}

/// An error that occurs if an unregistered field name was queried from a
/// [`Scheme`](struct@Scheme).
#[derive(Debug, PartialEq, Eq, Error)]
#[error("unknown field")]
pub struct UnknownFieldError;

/// An error that occurs if an unregistered function name was queried from a
/// [`Scheme`](struct@Scheme).
#[derive(Debug, PartialEq, Eq, Error)]
#[error("unknown function")]
pub struct UnknownFunctionError;

/// An error that occurs when previously defined field gets redefined.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("attempt to redefine field {0}")]
pub struct FieldRedefinitionError(String);

/// An error that occurs when previously defined function gets redefined.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("attempt to redefine function {0}")]
pub struct FunctionRedefinitionError(String);

/// An error that occurs when trying to redefine a field or function.
#[derive(Debug, PartialEq, Eq, Error)]
pub enum IdentifierRedefinitionError {
    /// An error that occurs when previously defined field gets redefined.
    #[error("{0}")]
    Field(#[source] FieldRedefinitionError),

    /// An error that occurs when previously defined function gets redefined.
    #[error("{0}")]
    Function(#[source] FunctionRedefinitionError),
}

#[derive(Clone, Copy, Debug)]
enum SchemeItem {
    Field(usize),
    Function(usize),
}

impl<T: FunctionDefinition + 'static> From<T> for Box<dyn FunctionDefinition> {
    fn from(func: T) -> Box<dyn FunctionDefinition> {
        Box::new(func)
    }
}

/// A structure to represent a list inside a [`scheme`](struct.Scheme.html).
///
/// See [`Scheme::get_list`](struct.Scheme.html#method.get_list).
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct List<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl<'s> List<'s> {
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    pub(crate) fn scheme(&self) -> &'s Scheme {
        self.scheme
    }

    pub(crate) fn definition(&self) -> &'s dyn ListDefinition {
        &*self.scheme.lists[self.index].1
    }
}

impl<'s> Debug for List<'s> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.scheme.lists[self.index])
    }
}

impl<'s> GetType for List<'s> {
    #[inline]
    fn get_type(&self) -> Type {
        self.scheme.lists[self.index].0
    }
}

/// An error that occurs when previously defined list gets redefined.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("attempt to redefine list for type {0:?}")]
pub struct ListRedefinitionError(Type);

type IdentifierName = Arc<str>;

/// The main registry for fields and their associated types.
///
/// This is necessary to provide typechecking for runtime values provided
/// to the [execution context](::ExecutionContext) and also to aid parser
/// in ambiguous contexts.
#[derive(Default, Debug)]
pub struct Scheme {
    fields: Vec<(IdentifierName, Type)>,
    functions: Vec<(IdentifierName, Box<dyn FunctionDefinition>)>,
    items: HashMap<IdentifierName, SchemeItem, FnvBuildHasher>,

    list_types: HashMap<Type, usize, FnvBuildHasher>,
    lists: Vec<(Type, Box<dyn ListDefinition>)>,
}

impl PartialEq for Scheme {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl Eq for Scheme {}

impl Hash for Scheme {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self as *const Scheme).hash(state);
    }
}

impl Serialize for Scheme {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.field_count()))?;
        for f in self.fields() {
            map.serialize_entry(f.name(), &f.get_type())?;
        }
        map.end()
    }
}

impl<'de> Deserialize<'de> for Scheme {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        use serde::de::Error;

        let mut scheme = Scheme::new();
        let map: HashMap<String, Type> = HashMap::<String, Type>::deserialize(deserializer)?;
        for (name, ty) in map {
            scheme.add_field(&name, ty).map_err(D::Error::custom)?;
        }
        Ok(scheme)
    }
}

impl<'s> Scheme {
    /// Creates a new scheme.
    pub fn new() -> Self {
        Default::default()
    }

    /// Returns the [`identifier`](struct@Identifier) with name [`name`]
    pub fn get(&'s self, name: &str) -> Option<Identifier<'s>> {
        self.items.get(name).map(move |item| match *item {
            SchemeItem::Field(index) => Identifier::Field(Field {
                scheme: self,
                index,
            }),
            SchemeItem::Function(index) => Identifier::Function(Function {
                scheme: self,
                index,
            }),
        })
    }

    /// Registers a field and its corresponding type.
    pub fn add_field<N: AsRef<str>>(
        &mut self,
        name: N,
        ty: Type,
    ) -> Result<(), IdentifierRedefinitionError> {
        match self.items.entry(name.as_ref().into()) {
            Entry::Occupied(entry) => match entry.get() {
                SchemeItem::Field(_) => Err(IdentifierRedefinitionError::Field(
                    FieldRedefinitionError(entry.key().to_string()),
                )),
                SchemeItem::Function(_) => Err(IdentifierRedefinitionError::Function(
                    FunctionRedefinitionError(entry.key().to_string()),
                )),
            },
            Entry::Vacant(entry) => {
                let index = self.fields.len();
                self.fields.push((entry.key().clone(), ty));
                entry.insert(SchemeItem::Field(index));
                Ok(())
            }
        }
    }

    /// Returns the [`field`](struct@Field) with name [`name`]
    pub fn get_field(&'s self, name: &str) -> Result<Field<'s>, UnknownFieldError> {
        match self.get(name) {
            Some(Identifier::Field(f)) => Ok(f),
            _ => Err(UnknownFieldError),
        }
    }

    /// Iterates over fields registered in the [`scheme`](struct@Scheme)
    #[inline]
    pub fn fields(&'s self) -> impl ExactSizeIterator<Item = Field<'s>> + 's {
        (0..self.fields.len()).map(|index| Field {
            scheme: self,
            index,
        })
    }

    /// Returns the number of fields in the [`scheme`](struct@Scheme)
    #[inline]
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// Returns the number of functions in the [`scheme`](struct@Scheme)
    #[inline]
    pub fn function_count(&self) -> usize {
        self.functions.len()
    }

    /// Registers a function
    pub fn add_function<N: AsRef<str>>(
        &mut self,
        name: N,
        function: impl Into<Box<dyn FunctionDefinition + 'static>>,
    ) -> Result<(), IdentifierRedefinitionError> {
        match self.items.entry(name.as_ref().into()) {
            Entry::Occupied(entry) => match entry.get() {
                SchemeItem::Field(_) => Err(IdentifierRedefinitionError::Field(
                    FieldRedefinitionError(entry.key().to_string()),
                )),
                SchemeItem::Function(_) => Err(IdentifierRedefinitionError::Function(
                    FunctionRedefinitionError(entry.key().to_string()),
                )),
            },
            Entry::Vacant(entry) => {
                let index = self.functions.len();
                self.functions.push((entry.key().clone(), function.into()));
                entry.insert(SchemeItem::Function(index));
                Ok(())
            }
        }
    }

    /// Returns the [`function`](struct@Function) with name [`name`]
    pub fn get_function(&'s self, name: &str) -> Result<Function<'s>, UnknownFunctionError> {
        match self.get(name) {
            Some(Identifier::Function(f)) => Ok(f),
            _ => Err(UnknownFunctionError),
        }
    }

    /// Iterates over functions registered in the [`scheme`](struct@Scheme)
    #[inline]
    pub fn functions(&'s self) -> impl ExactSizeIterator<Item = Function<'s>> + 's {
        (0..self.functions.len()).map(|index| Function {
            scheme: self,
            index,
        })
    }

    /// Parses a filter expression into an AST form.
    pub fn parse<'i>(&'s self, input: &'i str) -> Result<FilterAst<'s>, ParseError<'i>> {
        FilterParser::new(self).parse(input)
    }

    /// Parses a value expression into an AST form.
    pub fn parse_value<'i>(&'s self, input: &'i str) -> Result<FilterValueAst<'s>, ParseError<'i>> {
        FilterParser::new(self).parse_value(input)
    }

    /// Returns the number of lists in the [`scheme`](struct@Scheme)
    #[inline]
    pub fn list_count(&self) -> usize {
        self.lists.len()
    }

    /// Registers a new [`list`](trait.ListDefinition.html) for a given [`type`](enum.Type.html).
    pub fn add_list(
        &mut self,
        ty: Type,
        definition: Box<dyn ListDefinition>,
    ) -> Result<(), ListRedefinitionError> {
        match self.list_types.entry(ty) {
            Entry::Occupied(entry) => Err(ListRedefinitionError(*entry.key())),
            Entry::Vacant(entry) => {
                let index = self.lists.len();
                self.lists.push((ty, definition));
                entry.insert(index);
                Ok(())
            }
        }
    }

    /// Returns the [`list`](struct.List.html) for a given [`type`](enum.Type.html).
    pub fn get_list(&self, ty: &Type) -> Option<List<'_>> {
        self.list_types.get(ty).map(move |index| List {
            scheme: self,
            index: *index,
        })
    }

    /// Iterates over all registered [`lists`](trait.ListDefinition.html).
    pub fn lists(&self) -> impl ExactSizeIterator<Item = List<'_>> {
        (0..self.lists.len()).map(|index| List {
            scheme: self,
            index,
        })
    }
}

impl<N: AsRef<str>> FromIterator<(N, Type)> for Scheme {
    fn from_iter<T: IntoIterator<Item = (N, Type)>>(iter: T) -> Self {
        let mut scheme = Scheme::new();
        for (name, ty) in iter {
            scheme
                .add_field(name.as_ref(), ty)
                .map_err(|err| err.to_string())
                .unwrap();
        }
        scheme
    }
}

/// A convenience macro for constructing a [`Scheme`](struct@Scheme) with static
/// contents.
#[macro_export]
macro_rules! Scheme {
    ($($ns:ident $(. $field:ident)*: $ty:ident $(($subty:tt $($rest:tt)*))?),* $(,)*) => {
        $crate::Scheme::from_iter([$(
            (
                concat!(stringify!($ns) $(, ".", stringify!($field))*),
                Scheme!($ty $(($subty $($rest)*))?),
            )
        ),*])
    };
    ($ty:ident $(($subty:tt $($rest:tt)*))?) => {$crate::Type::$ty$(((Scheme!($subty $($rest)*)).into()))?};
}

#[test]
fn test_parse_error() {
    use crate::types::TypeMismatchError;
    use indoc::indoc;

    let scheme = &Scheme! {
        num: Int,
        arr: Array(Bool),
    };

    {
        let err = scheme.parse("xyz").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownIdentifier,
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
                ^^^ unknown identifier
                "#
            )
        );
    }

    {
        let err = scheme.parse("xyz\n").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownIdentifier,
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
                ^^^ unknown identifier
                "#
            )
        );
    }

    {
        let err = scheme.parse("\n\n    xyz").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::UnknownIdentifier,
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
                    ^^^ unknown identifier
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

    {
        let err = scheme
            .parse(indoc!(
                r#"
                arr and arr
                "#
            ))
            .unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: Type::Bool.into(),
                    actual: Type::Array(Type::Bool.into()),
                }),
                input: "arr and arr",
                line_number: 0,
                span_start: 11,
                span_len: 0,
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:12):
                arr and arr
                           ^ expected value of type {Type(Bool)}, but got Array(Bool)
                "#
            )
        );
    }

    {
        let err = scheme.parse_value(indoc!(r" arr[*] ")).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::TypeMismatch(TypeMismatchError {
                    expected: Type::Bool.into(),
                    actual: Type::Array(Type::Bool.into()),
                }),
                input: " arr[*] ",
                line_number: 0,
                span_start: 1,
                span_len: 6,
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:2):
                 arr[*] 
                 ^^^^^^ expected value of type {Type(Bool)}, but got Array(Bool)
                "#
            )
        );
    }
}

#[test]
fn test_parse_error_in_op() {
    use cidr::errors::NetworkParseError;
    use indoc::indoc;
    use std::{net::IpAddr, str::FromStr};

    let scheme = &Scheme! {
        num: Int,
        bool: Bool,
        str: Bytes,
        ip: Ip,
        str_arr: Array(Bytes),
        str_map: Map(Bytes),
    };

    {
        let err = scheme.parse("bool in {0}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::EOF,
                input: "bool in {0}",
                line_number: 0,
                span_start: 4,
                span_len: 7
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:5):
                bool in {0}
                    ^^^^^^^ unrecognised input
                "#
            )
        );
    }

    {
        let err = scheme.parse("bool in {127.0.0.1}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::EOF,
                input: "bool in {127.0.0.1}",
                line_number: 0,
                span_start: 4,
                span_len: 15
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:5):
                bool in {127.0.0.1}
                    ^^^^^^^^^^^^^^^ unrecognised input
                "#
            )
        );
    }

    {
        let err = scheme.parse("bool in {\"test\"}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::EOF,
                input: "bool in {\"test\"}",
                line_number: 0,
                span_start: 4,
                span_len: 12
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:5):
                bool in {"test"}
                    ^^^^^^^^^^^^ unrecognised input
                "#
            )
        );
    }

    {
        let err = scheme.parse("num in {127.0.0.1}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("digit"),
                input: "num in {127.0.0.1}",
                line_number: 0,
                span_start: 11,
                span_len: 7
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:12):
                num in {127.0.0.1}
                           ^^^^^^^ expected digit
                "#
            )
        );
    }

    {
        let err = scheme.parse("num in {\"test\"}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("digit"),
                input: "num in {\"test\"}",
                line_number: 0,
                span_start: 8,
                span_len: 7
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:9):
                num in {"test"}
                        ^^^^^^^ expected digit
                "#
            )
        );
    }
    {
        let err = scheme.parse("ip in {666}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ParseNetwork(
                    IpAddr::from_str("666")
                        .map_err(NetworkParseError::AddrParseError)
                        .unwrap_err()
                ),
                input: "ip in {666}",
                line_number: 0,
                span_start: 7,
                span_len: 3
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:8):
                ip in {666}
                       ^^^ couldn't parse address in network: invalid IP address syntax
                "#
            )
        );
    }
    {
        let err = scheme.parse("ip in {\"test\"}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("IP address character"),
                input: "ip in {\"test\"}",
                line_number: 0,
                span_start: 7,
                span_len: 7
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:8):
                ip in {"test"}
                       ^^^^^^^ expected IP address character
                "#
            )
        );
    }

    {
        let err = scheme.parse("str in {0}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ParseInt {
                    err: u8::from_str_radix("0}", 16).unwrap_err(),
                    radix: 16,
                },
                input: "str in {0}",
                line_number: 0,
                span_start: 8,
                span_len: 2
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:9):
                str in {0}
                        ^^ invalid digit found in string while parsing with radix 16
                "#
            )
        );
    }

    {
        let err = scheme.parse("str in {127.0.0.1}").unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("byte separator"),
                input: "str in {127.0.0.1}",
                line_number: 0,
                span_start: 10,
                span_len: 1
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:11):
                str in {127.0.0.1}
                          ^ expected byte separator
                "#
            )
        );
    }

    for pattern in &["0", "127.0.0.1", "\"test\""] {
        {
            let filter = format!("str_arr in {{{pattern}}}");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Array(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }

        {
            let filter = format!("str_map in {{{pattern}}}");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Map(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }
    }
}

#[test]
fn test_parse_error_ordering_op() {
    let scheme = &Scheme! {
        num: Int,
        bool: Bool,
        str: Bytes,
        ip: Ip,
        str_arr: Array(Bytes),
        str_map: Map(Bytes),
    };

    for op in &["eq", "ne", "ge", "le", "gt", "lt"] {
        {
            let filter = format!("num {op} 127.0.0.1");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::EOF,
                    input: &filter,
                    line_number: 0,
                    span_start: 10,
                    span_len: 6
                }
            );
        }

        {
            let filter = format!("num {op} \"test\"");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::ExpectedName("digit"),
                    input: &filter,
                    line_number: 0,
                    span_start: 7,
                    span_len: 6
                }
            );
        }
        {
            let filter = format!("str {op} 0");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::CountMismatch {
                        name: "character",
                        actual: 1,
                        expected: 2,
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 7,
                    span_len: 1
                }
            );
        }

        {
            let filter = format!("str {op} 256");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::ExpectedName("byte separator"),
                    input: &filter,
                    line_number: 0,
                    span_start: 9,
                    span_len: 1
                }
            );
        }

        {
            let filter = format!("str {op} 127.0.0.1");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::ExpectedName("byte separator"),
                    input: &filter,
                    line_number: 0,
                    span_start: 9,
                    span_len: 1,
                }
            );
        }

        {
            let filter = format!("str_arr {op} 0");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Array(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }

        {
            let filter = format!("str_arr {op} \"test\"");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Array(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }

        {
            let filter = format!("str_arr {op} 127.0.0.1");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Array(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }

        {
            let filter = format!("str_map {op} 0");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Map(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }

        {
            let filter = format!("str_map {op} \"test\"");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Map(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }

        {
            let filter = format!("str_map {op} 127.0.0.1");
            let err = scheme.parse(&filter).unwrap_err();
            assert_eq!(
                err,
                ParseError {
                    kind: LexErrorKind::UnsupportedOp {
                        lhs_type: Type::Map(Type::Bytes.into())
                    },
                    input: &filter,
                    line_number: 0,
                    span_start: 8,
                    span_len: 2
                }
            );
        }
    }
}

#[test]
fn test_field() {
    let scheme = &Scheme! {
        x: Bytes,
        x.y.z0: Int,
        is_TCP: Bool,
        map: Map(Bytes)
    };

    assert_ok!(
        Field::lex_with("x;", scheme),
        scheme.get_field("x").unwrap(),
        ";"
    );

    assert_ok!(
        Field::lex_with("x.y.z0-", scheme),
        scheme.get_field("x.y.z0").unwrap(),
        "-"
    );

    assert_ok!(
        Field::lex_with("is_TCP", scheme),
        scheme.get_field("is_TCP").unwrap(),
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
        scheme.add_field("foo", Type::Bytes).unwrap_err(),
        IdentifierRedefinitionError::Field(FieldRedefinitionError("foo".into()))
    )
}

#[test]
fn test_field_lex_indexes() {
    assert_ok!(FieldIndex::lex("0"), FieldIndex::ArrayIndex(0));
    assert_err!(
        FieldIndex::lex("-1"),
        LexErrorKind::ExpectedLiteral("expected positive integer as index"),
        "-1"
    );

    assert_ok!(
        FieldIndex::lex("\"cookies\""),
        FieldIndex::MapKey("cookies".into())
    );
}

#[test]
fn test_scheme_iter_fields() {
    let scheme = &Scheme! {
        x: Bytes,
        x.y.z0: Int,
        is_TCP: Bool,
        map: Map(Bytes)
    };

    let mut fields = scheme.fields().collect::<Vec<_>>();
    fields.sort_by(|f1, f2| f1.name().partial_cmp(f2.name()).unwrap());

    assert_eq!(
        fields,
        vec![
            scheme.get_field("is_TCP").unwrap(),
            scheme.get_field("map").unwrap(),
            scheme.get_field("x").unwrap(),
            scheme.get_field("x.y.z0").unwrap(),
        ]
    );
}
