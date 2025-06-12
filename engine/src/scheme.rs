use crate::{
    ast::{
        FilterAst, FilterValueAst,
        parse::{FilterParser, ParseError, ParserSettings},
    },
    functions::FunctionDefinition,
    lex::{Lex, LexErrorKind, LexResult, LexWith, expect, span, take_while},
    list_matcher::ListDefinition,
    types::{GetType, RhsValue, Type},
};
use fnv::FnvBuildHasher;
use serde::de::Visitor;
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
pub struct FieldRef<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl Serialize for FieldRef<'_> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl Debug for FieldRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FieldRef<'s> {
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

impl<'s> FieldRef<'s> {
    /// Returns the field's name as recorded in the [`Scheme`](struct@Scheme).
    #[inline]
    pub fn name(&self) -> &'s str {
        &self.scheme.inner.fields[self.index].name
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

    /// Converts to an owned [`Field`].
    #[inline]
    pub fn to_owned(&self) -> Field {
        Field {
            scheme: self.scheme.clone(),
            index: self.index,
        }
    }

    /// Reborrows the field relatively to the specified [`Scheme`] reference.
    ///
    /// Useful when you have a [`FieldRef`] borrowed from an owned [`Field`]
    /// but you need to extend/change it's lifetime.
    ///
    /// Panics if the field doesn't belong to the specified scheme.
    #[inline]
    pub fn reborrow(self, scheme: &Scheme) -> FieldRef<'_> {
        assert!(self.scheme == scheme);

        FieldRef {
            scheme,
            index: self.index,
        }
    }
}

impl GetType for FieldRef<'_> {
    #[inline]
    fn get_type(&self) -> Type {
        self.scheme.inner.fields[self.index].ty
    }
}

impl PartialEq<Field> for FieldRef<'_> {
    #[inline]
    fn eq(&self, other: &Field) -> bool {
        self.eq(&other.as_ref())
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
/// A structure to represent a field inside a [`Scheme`](struct@Scheme).
pub struct Field {
    scheme: Scheme,
    index: usize,
}

impl Serialize for Field {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl Debug for Field {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl Field {
    /// Returns the field's name as recorded in the [`Scheme`](struct@Scheme).
    #[inline]
    pub fn name(&self) -> &str {
        &self.scheme.inner.fields[self.index].name
    }

    /// Get the field's index in the [`Scheme`](struct@Scheme) identifier's list.
    #[inline]
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the [`Scheme`](struct@Scheme) to which this field belongs to.
    #[inline]
    pub fn scheme(&self) -> &Scheme {
        &self.scheme
    }

    /// Converts to a borrowed [`Field`].
    #[inline]
    pub fn as_ref(&self) -> FieldRef<'_> {
        FieldRef {
            scheme: &self.scheme,
            index: self.index,
        }
    }
}

impl GetType for Field {
    #[inline]
    fn get_type(&self) -> Type {
        self.scheme.inner.fields[self.index].ty
    }
}

impl PartialEq<FieldRef<'_>> for Field {
    #[inline]
    fn eq(&self, other: &FieldRef<'_>) -> bool {
        self.as_ref().eq(other)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
/// A structure to represent a function inside a [`Scheme`](struct@Scheme).
pub struct FunctionRef<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl Serialize for FunctionRef<'_> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl Debug for FunctionRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl<'i, 's> LexWith<'i, &'s Scheme> for FunctionRef<'s> {
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

impl<'s> FunctionRef<'s> {
    /// Returns the function's name as recorded in the [`Scheme`](struct@Scheme).
    #[inline]
    pub fn name(&self) -> &'s str {
        &self.scheme.inner.functions[self.index].0
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
        &*self.scheme.inner.functions[self.index].1
    }

    /// Converts to an owned [`Function`].
    #[inline]
    pub fn to_owned(&self) -> Function {
        Function {
            scheme: self.scheme.clone(),
            index: self.index,
        }
    }

    /// Reborrows the function relatively to the specified [`Scheme`] reference.
    ///
    /// Useful when you have a [`FunctionRef`] borrowed from an owned [`Function`]
    /// but you need to extend/change it's lifetime.
    ///
    /// Panics if the function doesn't belong to the specified scheme.
    #[inline]
    pub fn reborrow(self, scheme: &Scheme) -> FunctionRef<'_> {
        assert!(self.scheme == scheme);

        FunctionRef {
            scheme,
            index: self.index,
        }
    }
}

impl PartialEq<Function> for FunctionRef<'_> {
    #[inline]
    fn eq(&self, other: &Function) -> bool {
        self.eq(&other.as_ref())
    }
}

#[derive(PartialEq, Eq, Clone, Hash)]
/// A structure to represent a function inside a [`Scheme`](struct@Scheme).
pub struct Function {
    scheme: Scheme,
    index: usize,
}

impl Serialize for Function {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.name().serialize(ser)
    }
}

impl Debug for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

impl Function {
    /// Returns the function's name as recorded in the [`Scheme`](struct@Scheme).
    #[inline]
    pub fn name(&self) -> &str {
        &self.scheme.inner.functions[self.index].0
    }

    /// Get the function's index in the [`Scheme`](struct@Scheme) identifier's list.
    #[inline]
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the [`Scheme`](struct@Scheme) to which this function belongs to.
    #[inline]
    pub fn scheme(&self) -> &Scheme {
        &self.scheme
    }

    #[inline]
    pub(crate) fn as_definition(&self) -> &dyn FunctionDefinition {
        &*self.scheme.inner.functions[self.index].1
    }

    /// Converts to a borrowed [`Function`].
    #[inline]
    pub fn as_ref(&self) -> FunctionRef<'_> {
        FunctionRef {
            scheme: &self.scheme,
            index: self.index,
        }
    }
}

impl PartialEq<FunctionRef<'_>> for Function {
    #[inline]
    fn eq(&self, other: &FunctionRef<'_>) -> bool {
        self.as_ref().eq(other)
    }
}

/// An enum to represent an entry inside a [`Scheme`](struct@Scheme).
/// It can be either a [`Field`](struct@Field) or a [`Function`](struct@Function).
#[derive(Debug)]
pub(crate) enum Identifier<'s> {
    /// Identifier is a [`Field`](struct@Field)
    Field(FieldRef<'s>),
    /// Identifier is a [`Function`](struct@Function)
    Function(FunctionRef<'s>),
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

/// A structure to represent a list inside a [`scheme`](struct.Scheme.html).
///
/// See [`Scheme::get_list`](struct.Scheme.html#method.get_list).
#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct ListRef<'s> {
    scheme: &'s Scheme,
    index: usize,
}

impl<'s> ListRef<'s> {
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    pub(crate) fn scheme(&self) -> &'s Scheme {
        self.scheme
    }

    pub(crate) fn definition(&self) -> &'s dyn ListDefinition {
        &*self.scheme.inner.lists[self.index].1
    }

    /// Converts to an owned [`List`].
    #[inline]
    pub fn to_owned(&self) -> List {
        List {
            scheme: self.scheme.clone(),
            index: self.index,
        }
    }

    /// Reborrows the list relatively to the specified [`Scheme`] reference.
    ///
    /// Useful when you have a [`ListRef`] borrowed from an owned [`List`]
    /// but you need to extend/change it's lifetime.
    ///
    /// Panics if the list doesn't belong to the specified scheme.
    #[inline]
    pub fn reborrow(self, scheme: &Scheme) -> ListRef<'_> {
        assert!(self.scheme == scheme);

        ListRef {
            scheme,
            index: self.index,
        }
    }
}

impl Debug for ListRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.scheme.inner.lists[self.index])
    }
}

impl GetType for ListRef<'_> {
    #[inline]
    fn get_type(&self) -> Type {
        self.scheme.inner.lists[self.index].0
    }
}

impl PartialEq<List> for ListRef<'_> {
    #[inline]
    fn eq(&self, other: &List) -> bool {
        self.eq(&other.as_ref())
    }
}

/// A structure to represent a list inside a [`scheme`](struct.Scheme.html).
///
/// See [`Scheme::get_list`](struct.Scheme.html#method.get_list).
#[derive(PartialEq, Eq, Clone, Hash)]
pub struct List {
    scheme: Scheme,
    index: usize,
}

impl List {
    #[inline]
    pub(crate) fn index(&self) -> usize {
        self.index
    }

    #[inline]
    pub(crate) fn scheme(&self) -> &Scheme {
        &self.scheme
    }

    /// Converts to a borrowed [`ListRef`].
    #[inline]
    pub fn as_ref(&self) -> ListRef<'_> {
        ListRef {
            scheme: &self.scheme,
            index: self.index,
        }
    }
}

impl Debug for List {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.scheme.inner.lists[self.index])
    }
}

impl GetType for List {
    #[inline]
    fn get_type(&self) -> Type {
        self.scheme.inner.lists[self.index].0
    }
}

impl PartialEq<ListRef<'_>> for List {
    #[inline]
    fn eq(&self, other: &ListRef<'_>) -> bool {
        self.as_ref().eq(other)
    }
}

/// An error that occurs when previously defined list gets redefined.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("attempt to redefine list for type {0:?}")]
pub struct ListRedefinitionError(Type);

type IdentifierName = Arc<str>;

#[derive(Debug, PartialEq)]
struct FieldDefinition {
    name: IdentifierName,
    ty: Type,
}

/// A builder for a [`Scheme`].
#[derive(Default, Debug)]
pub struct SchemeBuilder {
    fields: Vec<FieldDefinition>,
    functions: Vec<(IdentifierName, Box<dyn FunctionDefinition>)>,
    items: HashMap<IdentifierName, SchemeItem, FnvBuildHasher>,

    list_types: HashMap<Type, usize, FnvBuildHasher>,
    lists: Vec<(Type, Box<dyn ListDefinition>)>,
}

impl SchemeBuilder {
    /// Creates a new scheme.
    pub fn new() -> Self {
        Default::default()
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
                self.fields.push(FieldDefinition {
                    name: entry.key().clone(),
                    ty,
                });
                entry.insert(SchemeItem::Field(index));
                Ok(())
            }
        }
    }

    /// Registers a function
    pub fn add_function<N: AsRef<str>>(
        &mut self,
        name: N,
        function: impl FunctionDefinition + 'static,
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
                self.functions
                    .push((entry.key().clone(), Box::new(function)));
                entry.insert(SchemeItem::Function(index));
                Ok(())
            }
        }
    }

    /// Registers a new [`list`](trait.ListDefinition.html) for a given [`type`](enum.Type.html).
    pub fn add_list(
        &mut self,
        ty: Type,
        definition: impl ListDefinition + 'static,
    ) -> Result<(), ListRedefinitionError> {
        match self.list_types.entry(ty) {
            Entry::Occupied(entry) => Err(ListRedefinitionError(*entry.key())),
            Entry::Vacant(entry) => {
                let index = self.lists.len();
                self.lists.push((ty, Box::new(definition)));
                entry.insert(index);
                Ok(())
            }
        }
    }

    /// Build a new [`Scheme`] from this builder.
    pub fn build(self) -> Scheme {
        Scheme {
            inner: Arc::new(self),
        }
    }
}

impl<N: AsRef<str>> FromIterator<(N, Type)> for SchemeBuilder {
    fn from_iter<T: IntoIterator<Item = (N, Type)>>(iter: T) -> Self {
        let mut builder = SchemeBuilder::new();
        for (name, ty) in iter {
            builder
                .add_field(name.as_ref(), ty)
                .map_err(|err| err.to_string())
                .unwrap();
        }
        builder
    }
}

/// The main registry for fields and their associated types.
///
/// This is necessary to provide typechecking for runtime values provided
/// to the [`crate::ExecutionContext`] and also to aid parser
/// in ambiguous contexts.
#[derive(Clone, Debug)]
pub struct Scheme {
    inner: Arc<SchemeBuilder>,
}

impl PartialEq for Scheme {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.inner, &other.inner)
    }
}

impl Eq for Scheme {}

impl Hash for Scheme {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.inner).hash(state);
    }
}

#[derive(Deserialize, Serialize)]
struct SerdeField {
    #[serde(rename = "type")]
    ty: Type,
}

impl Serialize for Scheme {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let fields = self.fields();
        let mut map = serializer.serialize_map(Some(fields.len()))?;
        for f in fields {
            map.serialize_entry(f.name(), &SerdeField { ty: f.get_type() })?;
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

        struct FieldMapVisitor;

        impl<'de> Visitor<'de> for FieldMapVisitor {
            type Value = SchemeBuilder;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a wirefilter scheme")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let mut builder = SchemeBuilder::new();
                while let Some((name, SerdeField { ty })) = map.next_entry::<&str, SerdeField>()? {
                    builder.add_field(name, ty).map_err(A::Error::custom)?;
                }

                Ok(builder)
            }
        }

        deserializer
            .deserialize_map(FieldMapVisitor)
            .map(|builder| builder.build())
    }
}

impl<'s> Scheme {
    /// Returns the [`identifier`](enum@Identifier) with the specified `name`.
    pub(crate) fn get(&'s self, name: &str) -> Option<Identifier<'s>> {
        self.inner.items.get(name).map(move |item| match *item {
            SchemeItem::Field(index) => Identifier::Field(FieldRef {
                scheme: self,
                index,
            }),
            SchemeItem::Function(index) => Identifier::Function(FunctionRef {
                scheme: self,
                index,
            }),
        })
    }

    /// Returns the [`field`](struct@Field) with the specified `name`.
    pub fn get_field(&'s self, name: &str) -> Result<FieldRef<'s>, UnknownFieldError> {
        match self.get(name) {
            Some(Identifier::Field(f)) => Ok(f),
            _ => Err(UnknownFieldError),
        }
    }

    /// Iterates over fields registered in the [`scheme`](struct@Scheme).
    #[inline]
    pub fn fields(&'s self) -> impl ExactSizeIterator<Item = FieldRef<'s>> + 's {
        (0..self.inner.fields.len()).map(|index| FieldRef {
            scheme: self,
            index,
        })
    }

    /// Returns the number of fields in the [`scheme`](struct@Scheme).
    #[inline]
    pub fn field_count(&self) -> usize {
        self.inner.fields.len()
    }

    /// Returns the number of functions in the [`scheme`](struct@Scheme).
    #[inline]
    pub fn function_count(&self) -> usize {
        self.inner.functions.len()
    }

    /// Returns the [`function`](struct@Function) with the specified `name`.
    pub fn get_function(&'s self, name: &str) -> Result<FunctionRef<'s>, UnknownFunctionError> {
        match self.get(name) {
            Some(Identifier::Function(f)) => Ok(f),
            _ => Err(UnknownFunctionError),
        }
    }

    /// Iterates over functions registered in the [`scheme`](struct@Scheme).
    #[inline]
    pub fn functions(&'s self) -> impl ExactSizeIterator<Item = FunctionRef<'s>> + 's {
        (0..self.inner.functions.len()).map(|index| FunctionRef {
            scheme: self,
            index,
        })
    }

    /// Creates a new parser with default settings.
    pub fn parser(&self) -> FilterParser<'_> {
        FilterParser::new(self)
    }

    /// Creates a new parser with the specified settings.
    pub fn parser_with_settings(&self, settings: ParserSettings) -> FilterParser<'_> {
        FilterParser::with_settings(self, settings)
    }

    /// Parses a filter expression into an AST form.
    pub fn parse<'i>(&'s self, input: &'i str) -> Result<FilterAst, ParseError<'i>> {
        FilterParser::new(self).parse(input)
    }

    /// Parses a value expression into an AST form.
    pub fn parse_value<'i>(&'s self, input: &'i str) -> Result<FilterValueAst, ParseError<'i>> {
        FilterParser::new(self).parse_value(input)
    }

    /// Returns the number of lists in the [`scheme`](struct@Scheme)
    #[inline]
    pub fn list_count(&self) -> usize {
        self.inner.lists.len()
    }

    /// Returns the [`list`](struct.List.html) for a given [`type`](enum.Type.html).
    pub fn get_list(&self, ty: &Type) -> Option<ListRef<'_>> {
        self.inner.list_types.get(ty).map(move |index| ListRef {
            scheme: self,
            index: *index,
        })
    }

    /// Iterates over all registered [`lists`](trait.ListDefinition.html).
    pub fn lists(&self) -> impl ExactSizeIterator<Item = ListRef<'_>> + use<'_> {
        (0..self.inner.lists.len()).map(|index| ListRef {
            scheme: self,
            index,
        })
    }
}

/// A convenience macro for constructing a [`SchemeBuilder`] with static contents.
#[macro_export]
macro_rules! Scheme {
    ($($ns:ident $(. $field:ident)*: $ty:ident $(($subty:tt $($rest:tt)*))?),* $(,)*) => {
        $crate::SchemeBuilder::from_iter([$(
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
    use crate::ConcatFunction;
    use crate::types::{ExpectedTypeList, TypeMismatchError};
    use indoc::indoc;

    let mut builder = Scheme! {
        num: Int,
        str: Bytes,
        arr: Array(Bool),
    };

    builder
        .add_function("concat", ConcatFunction::new())
        .unwrap();

    let scheme = builder.build();

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
                           ^ expected value of type Bool, but got Array<Bool>
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
                 ^^^^^^ expected value of type Bool, but got Array<Bool>
                "#
            )
        );
    }

    {
        let err = scheme.parse(indoc!(r"str in {")).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::EOF,
                input: "str in {",
                line_number: 0,
                span_start: 8,
                span_len: 0,
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:9):
                str in {
                        ^ unrecognised input
                "#
            )
        );
    }

    {
        let err = scheme.parse(indoc!(r#"str in {"a""#)).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::EOF,
                input: r#"str in {"a""#,
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
                str in {"a"
                           ^ unrecognised input
                "#
            )
        );
    }

    {
        let err = scheme.parse(indoc!(r"num in {")).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::ExpectedName("digit"),
                input: "num in {",
                line_number: 0,
                span_start: 8,
                span_len: 0,
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:9):
                num in {
                        ^ expected digit
                "#
            )
        );
    }

    {
        let err = scheme.parse(indoc!(r"concat(0, 0) == 0")).unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: LexErrorKind::InvalidArgumentType {
                    index: 0,
                    mismatch: TypeMismatchError {
                        expected: ExpectedTypeList::from(
                            crate::functions::concat::EXPECTED_TYPES.into_iter()
                        ),
                        actual: Type::Int,
                    },
                },
                input: "concat(0, 0) == 0",
                line_number: 0,
                span_start: 7,
                span_len: 1,
            }
        );
        assert_eq!(
            err.to_string(),
            indoc!(
                r#"
                Filter parsing error (1:8):
                concat(0, 0) == 0
                       ^ invalid type of argument #0: expected value of type Bytes or Array<_>, but got Int
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
    }
    .build();

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
    }
    .build();

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
    }
    .build();

    assert_ok!(
        FieldRef::lex_with("x;", scheme),
        scheme.get_field("x").unwrap(),
        ";"
    );

    assert_ok!(
        FieldRef::lex_with("x.y.z0-", scheme),
        scheme.get_field("x.y.z0").unwrap(),
        "-"
    );

    assert_ok!(
        FieldRef::lex_with("is_TCP", scheme),
        scheme.get_field("is_TCP").unwrap(),
        ""
    );

    assert_err!(
        FieldRef::lex_with("x..y", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        ".y"
    );

    assert_err!(
        FieldRef::lex_with("x.#", scheme),
        LexErrorKind::ExpectedName("identifier character"),
        "#"
    );

    assert_err!(
        FieldRef::lex_with("x.y.z;", scheme),
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
    let mut builder = Scheme! { foo: Int };

    assert_eq!(
        builder.add_field("foo", Type::Bytes),
        Err(IdentifierRedefinitionError::Field(FieldRedefinitionError(
            "foo".into()
        )))
    );
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
    }
    .build();

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

#[test]
fn test_scheme_json_serialization() {
    let scheme = Scheme! {
        bytes: Bytes,
        int: Int,
        bool: Bool,
        ip: Ip,
        map_of_bytes: Map(Bytes),
        map_of_array_of_bytes: Map(Array(Bytes)),
        array_of_bytes: Array(Bytes),
        array_of_map_of_bytes: Array(Map(Bytes)),
    }
    .build();

    let json = serde_json::to_string(&scheme).unwrap();

    let new_scheme = serde_json::from_str::<Scheme>(&json).unwrap();

    assert_eq!(scheme.inner.fields, new_scheme.inner.fields);
}
