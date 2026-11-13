//! Value interfaces, concrete collection traversal, and value conversion.
//!
//! Implement [`Value`] to associate storage with a [`FieldValueType`] and an
//! engine-provided reader. Custom containers implement [`ArrayValue`] or
//! [`MapValue`] and select [`ArrayRead`] or [`MapRead`]. Comparison execution is
//! internal: scalar comparison returns an optional boolean, while array
//! comparison appends results to an ordinary [`TypedArray<bool>`].

use crate::lhs_types::append_stored_lhs_at;
pub use crate::lhs_types::{LhsValueRead, LhsValueType};
use crate::{CompoundType, FieldIndex, LhsValue, Type, TypedArray};
use std::borrow::{Borrow, Cow};
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::net::IpAddr;

/// A path incompatible with the declared value type.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("unsupported value operation: {0}")]
pub struct ValueError(pub &'static str);

/// A Wirefilter value type, including recursively composed containers.
///
/// Types such as [`Bytes`] and [`Array<Bytes>`] describe the value independently
/// of its Rust storage and borrow lifetime. [`Self::TYPE`] is the corresponding
/// [`Type`] used by the scheme and compiler.
///
/// Paths contain owned keys and concrete child paths. Their lifetimes are
/// independent of runtime storage or borrowed selection descriptors.
pub trait ValueType {
    /// Whether this type is a scalar, for one-pass output-capacity hints.
    const IS_PRIMITIVE: bool;

    /// Concrete traversal independent of a scalar predicate.
    type Path: Send + Sync + 'static;

    /// Wirefilter's corresponding logical type.
    const TYPE: Type;

    /// Validate a path ending at the custom predicate's declared scalar type.
    fn compile_path(path: &[FieldIndex], input_type: Type) -> Result<Self::Path, ValueError>;
}

/// Type and traversal of a field, resolved when its filter is compiled.
///
/// Every static [`ValueType`] implements this trait automatically. [`LhsValueType`]
/// instead obtains its type from the scheme, allowing one provider to expose
/// stored values with arbitrary collection nesting. Collection elements exposed
/// through [`ArrayValue`] or [`MapValue`] still require a static [`ValueType`]; a
/// scheme-typed value is a complete field.
pub trait FieldValueType {
    /// A fixed getter type, or `None` when the scheme supplies the field's type.
    const STATIC_TYPE: Option<Type>;

    /// Whether the reader can compare a selected collection directly.
    /// Typed collections normally convert for custom collection comparisons.
    const DIRECT_COLLECTION_COMPARISON: bool = false;

    /// Compiled traversal, independent of request data and the field getter.
    type Path: Send + Sync + 'static;

    /// Validate traversal from the declared field type to the comparator's input.
    fn compile_field_path(
        field_type: Type,
        path: Vec<FieldIndex>,
        input_type: Type,
    ) -> Result<Self::Path, ValueError>;
}

impl<S: ValueType> FieldValueType for S {
    type Path = S::Path;

    const STATIC_TYPE: Option<Type> = Some(S::TYPE);

    fn compile_field_path(
        field_type: Type,
        path: Vec<FieldIndex>,
        input_type: Type,
    ) -> Result<Self::Path, ValueError> {
        if field_type != S::TYPE {
            return Err(ValueError("getter type differs from declared field type"));
        }
        S::compile_path(&path, input_type)
    }
}

/// A statically dispatched comparison over values and their scalar representations.
///
/// The compiler selects the scalar comparison method from the validated path's
/// type. Implementations override that method. A compiler adapts a comparison
/// that needs the evaluation context to this interface by
/// borrowing its evaluation context; traversal does not erase the predicate or
/// construct a value enum for each element.
pub(crate) trait ValuePredicate {
    /// Compare an existing stored value, including a selected collection.
    fn lhs(&self, _: &LhsValue<'_>) -> bool {
        panic!("predicate does not accept stored values")
    }

    /// Compare a borrowed byte string.
    fn bytes(&self, _: &[u8]) -> bool {
        panic!("predicate does not accept byte strings")
    }

    /// Compare an integer.
    fn int(&self, _: i64) -> bool {
        panic!("predicate does not accept integers")
    }

    /// Compare an IP address.
    fn ip(&self, _: IpAddr) -> bool {
        panic!("predicate does not accept IP addresses")
    }

    /// Compare a boolean.
    fn boolean(&self, _: bool) -> bool {
        panic!("predicate does not accept booleans")
    }
}

/// A value selects its logical type and an engine-provided reader.
///
/// A custom array implements [`ArrayValue`] and selects [`ArrayRead`]; a custom
/// map implements [`MapValue`] and selects [`MapRead`]. Neither implementation
/// needs to implement comparison algorithms or construct erased value enums.
///
/// Byte storage includes `Vec<u8>`, `Cow<[u8]>`, and [`crate::Bytes`]. The optional
/// `bytes` feature also supports `bytes::Bytes`, including inside arrays and maps.
pub trait Value {
    /// Logical type, independent of the borrow lifetime of this provider.
    type ValueType: FieldValueType;

    /// Engine-provided reader for the selected type and storage interface.
    ///
    /// Select a supplied reader such as [`BytesRead`], [`ArrayRead`], or
    /// [`MapRead`]. Its execution interface is internal to Wirefilter;
    /// applications customize their storage through the collection traits.
    // The private bound intentionally permits selecting supported readers while
    // keeping their comparison implementation inside Wirefilter.
    #[allow(private_bounds)]
    type Read: ReadValue<Self, Self::ValueType>;
}

/// Convert a value into the representation used by general value expressions.
///
/// Direct comparisons through the value reader do not require conversion.
/// Application arrays and maps materialize their container structure when passed
/// to functions or other operations requiring an [`LhsValue`]. Borrowed values
/// retain references to byte payloads.
///
/// A descriptor returned by value may implement this trait with the default method:
/// the resulting value owns its payloads and cannot borrow the temporary descriptor.
/// Descriptors that retain longer-lived references can override it to keep those
/// payloads borrowed, as [`SliceView`] does.
pub trait IntoLhsValue<'a>: Value + Sized {
    /// Whether converting a collection builds container storage.
    ///
    /// The compiler uses this hint to memoize converted non-mapped function
    /// arguments. Borrowing existing Wirefilter containers is cheap and returns
    /// `false`; application arrays and maps retain the default. This does not
    /// change whether the value can be passed to a function.
    const MATERIALIZES_COLLECTIONS: bool = true;

    /// Consume the value, preserving references valid for `'a` where possible.
    fn into_lhs(self) -> LhsValue<'a> {
        Self::Read::to_lhs(&self).into_owned()
    }

    /// Consume the value and convert the selection reached by keys and indexes.
    ///
    /// Borrowed values select directly from their source storage and convert only
    /// the selected value.
    /// The default preserves custom conversion and ownership behavior by calling
    /// [`Self::into_lhs`] before indexing. Borrowing descriptors can override this
    /// method to select first, as [`SliceView`] does.
    ///
    /// Returns `None` for a missing key or index. An empty path converts the whole
    /// value. Paths must contain valid array indexes and map keys, not `[*]`;
    /// incompatible paths panic, as they indicate an invalid compiled expression.
    #[inline]
    fn into_lhs_at(self, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        self.into_lhs().extract_nested(indexes)
    }

    /// Consume the value and append selections reached by keys, indexes, and `[*]`.
    ///
    /// Missing children contribute no values. The `[*]` operator visits arrays in
    /// array order and maps in the byte-key order required by [`MapValue::values`].
    /// An empty path appends the whole value, including its container structure.
    /// Existing entries in `output` are preserved.
    ///
    /// Borrowed values select directly from their source storage and convert only
    /// the selected values.
    /// The default selects the fixed prefix through [`Self::into_lhs_at`], then
    /// traverses the converted value, preserving custom conversion and ownership.
    /// Borrowing descriptors can override this method to retain their source
    /// lifetime during traversal, as [`SliceView`] does.
    ///
    /// Paths must be compatible with the declared type; incompatible paths panic.
    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        let prefix = indexes
            .iter()
            .position(|index| *index == FieldIndex::MapEach)
            .unwrap_or(indexes.len());
        if let Some(value) = self.into_lhs_at(&indexes[..prefix]) {
            append_stored_lhs_at(value, &indexes[prefix..], output);
        }
    }
}

impl<'a, 'data: 'a, T: Value + ?Sized> IntoLhsValue<'a> for &'data T {
    const MATERIALIZES_COLLECTIONS: bool = T::Read::MATERIALIZES_COLLECTIONS;

    #[inline]
    fn into_lhs(self) -> LhsValue<'a> {
        T::Read::to_lhs(self)
    }

    #[inline]
    fn into_lhs_at(self, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        T::Read::to_lhs_at(self, indexes)
    }

    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        T::Read::append_lhs_at(self, indexes, output);
    }
}

/// Internal conversion and comparison operations for a value.
///
/// The compiler chooses scalar or array evaluation before constructing the
/// closure. Both operations preserve concrete storage and predicate types.
pub(crate) trait ReadValue<V: ?Sized, S: FieldValueType> {
    /// Cost of converting borrowed storage, used by `IntoLhsValue for &T`.
    const MATERIALIZES_COLLECTIONS: bool = true;

    /// Borrow storage as an ordinary value of its declared field type.
    fn to_lhs(value: &V) -> LhsValue<'_>;

    /// Convert a selection without materializing its ancestor containers.
    /// Container readers consume child projections so temporary descriptors can
    /// preserve their own payload lifetime through `IntoLhsValue`.
    #[inline]
    fn to_lhs_at<'a>(value: &'a V, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        Self::to_lhs(value).extract_nested(indexes)
    }

    /// Append selected values without materializing their ancestor containers.
    /// Child projections are consumed so borrowed descriptors retain their source
    /// lifetime instead of borrowing a temporary on the traversal stack.
    #[inline]
    fn append_lhs_at<'a>(value: &'a V, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        assert!(indexes.is_empty(), "path continues beyond scalar");
        output.push(Self::to_lhs(value));
    }

    /// Compare the value selected by a path containing only indexes and keys.
    /// A missing index or key returns `None`; `[*]` is a compiler error.
    fn compare_one<P: ValuePredicate + ?Sized>(
        value: &V,
        path: &S::Path,
        predicate: &P,
    ) -> Option<bool>;

    /// Append comparisons in traversal order, skipping missing indexes and keys.
    /// Scalar readers append one result; container readers also handle `[*]`.
    #[inline]
    fn compare_vec<P: ValuePredicate + ?Sized>(
        value: &V,
        path: &S::Path,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        if let Some(result) = Self::compare_one(value, path, predicate) {
            output.push(result);
        }
    }
}

/// Compare a scalar selection without constructing a result collector.
#[inline]
pub(crate) fn compare_one<V: Value + ?Sized, P: ValuePredicate + ?Sized>(
    value: &V,
    path: &<V::ValueType as FieldValueType>::Path,
    predicate: &P,
) -> Option<bool> {
    V::Read::compare_one(value, path, predicate)
}

/// Append comparisons for a possibly nested array or map selection.
#[inline]
pub(crate) fn compare_vec<V: Value + ?Sized, P: ValuePredicate + ?Sized>(
    value: &V,
    path: &<V::ValueType as FieldValueType>::Path,
    predicate: &P,
    output: &mut TypedArray<'static, bool>,
) {
    V::Read::compare_vec(value, path, predicate, output);
}

/// A concrete array projection. Elements can be references or borrowed descriptors.
pub trait ArrayValue {
    /// Stable logical type of each element.
    type Element: ValueType;

    /// A projection tied to the borrow of the container.
    type Item<'a>: Value<ValueType = Self::Element> + IntoLhsValue<'a>
    where
        Self: 'a;

    /// A concrete iterator; no trait-object iterator or exact-length scan is needed.
    type Iter<'a>: Iterator<Item = Self::Item<'a>>
    where
        Self: 'a;

    /// Retrieve a single element without erasing its type.
    fn get(&self, index: usize) -> Option<Self::Item<'_>>;

    /// Iterate in logical array order.
    fn iter(&self) -> Self::Iter<'_>;
}

/// A byte-keyed map with concrete value projections.
pub trait MapValue {
    /// Stable logical type of each map value.
    type Element: ValueType;

    /// A reference or descriptor returned by value.
    type Item<'a>: Value<ValueType = Self::Element> + IntoLhsValue<'a>
    where
        Self: 'a;

    /// A concrete iterator over map values.
    type Iter<'a>: Iterator<Item = Self::Item<'a>>
    where
        Self: 'a;

    /// Look up a key with exact byte equality, without case normalization.
    fn get(&self, key: &[u8]) -> Option<Self::Item<'_>>;

    /// Iterate values in ascending lexicographic order of their exact byte keys.
    ///
    /// This must match ordinary Wirefilter maps, including after conversion for
    /// function arguments. Vector logical operations combine results by position;
    /// a different iteration order can change results even through an identity
    /// function. Adapters over differently ordered storage must supply this order.
    fn values(&self) -> Self::Iter<'_>;

    /// Visit key-value pairs when a general value expression needs a stored map.
    ///
    /// Keys use exact bytes and must be unique. Keys may be temporary: conversion
    /// copies each key, while the returned value may borrow the map for `'a`.
    fn for_each_entry<'a>(&'a self, visitor: impl FnMut(&[u8], Self::Item<'a>));
}

/// An array type composed with any other type.
pub struct Array<S>(PhantomData<S>);
/// A map type composed with any other type.
pub struct Map<S>(PhantomData<S>);

/// A concrete array access followed by a concrete child path.
///
/// This is [`ValueType::Path`] for [`Array<S>`], with `P = S::Path`.
/// [`ValueType::compile_path`] constructs it during expression compilation;
/// [`ArrayRead`] follows it during evaluation. The path owns no request data.
/// Indices retain the parsed [`FieldIndex::ArrayIndex`] width to keep compiled
/// paths compact, and are converted to `usize` only when accessing a collection.
pub enum ArrayPath<P> {
    /// Select one index, then follow the child path if the element exists.
    Index(u32, P),
    /// Follow the child path for each element in array order.
    Each(P),
}

/// A concrete map access followed by a concrete child path.
///
/// This is [`ValueType::Path`] for [`Map<S>`], with `P = S::Path`.
/// [`ValueType::compile_path`] constructs it during expression compilation;
/// [`MapRead`] follows it during evaluation. Keys are owned so the path can
/// outlive both the parsed expression and any request.
pub enum MapPath<P> {
    /// Select an exact byte key, then follow the child path if the key exists.
    Key(Box<[u8]>, P),
    /// Follow the child path for each value in ascending byte-key order.
    Each(P),
}

impl<S: ValueType> ValueType for Array<S> {
    type Path = ArrayPath<S::Path>;

    const IS_PRIMITIVE: bool = false;
    const TYPE: Type = Type::Array(CompoundType::from_type(S::TYPE));

    fn compile_path(path: &[FieldIndex], input_type: Type) -> Result<Self::Path, ValueError> {
        let (step, rest) = path
            .split_first()
            .ok_or(ValueError("array requires an index or [*]"))?;
        match step {
            FieldIndex::ArrayIndex(index) => {
                Ok(ArrayPath::Index(*index, S::compile_path(rest, input_type)?))
            }
            FieldIndex::MapEach => Ok(ArrayPath::Each(S::compile_path(rest, input_type)?)),
            FieldIndex::MapKey(_) => Err(ValueError("map key used on array")),
        }
    }
}

impl<S: ValueType> ValueType for Map<S> {
    type Path = MapPath<S::Path>;

    const IS_PRIMITIVE: bool = false;
    const TYPE: Type = Type::Map(CompoundType::from_type(S::TYPE));

    fn compile_path(path: &[FieldIndex], input_type: Type) -> Result<Self::Path, ValueError> {
        let (step, rest) = path
            .split_first()
            .ok_or(ValueError("map requires a key or [*]"))?;
        match step {
            FieldIndex::MapKey(key) => Ok(MapPath::Key(
                key.as_bytes().into(),
                S::compile_path(rest, input_type)?,
            )),
            FieldIndex::MapEach => Ok(MapPath::Each(S::compile_path(rest, input_type)?)),
            FieldIndex::ArrayIndex(_) => Err(ValueError("array index used on map")),
        }
    }
}

/// Engine reader for any concrete [`ArrayValue`] implementation.
pub struct ArrayRead;

impl<A: ArrayValue + ?Sized> ReadValue<A, Array<A::Element>> for ArrayRead {
    fn to_lhs(array: &A) -> LhsValue<'_> {
        crate::Array::try_from_iter(A::Element::TYPE, array.iter().map(IntoLhsValue::into_lhs))
            .expect("array items must match their declared type")
            .into()
    }

    #[inline]
    fn to_lhs_at<'a>(array: &'a A, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        match indexes.split_first() {
            None => Some(Self::to_lhs(array)),
            Some((FieldIndex::ArrayIndex(index), rest)) => {
                array.get(*index as usize)?.into_lhs_at(rest)
            }
            Some(_) => panic!("array selection requires an array index"),
        }
    }

    #[inline]
    fn append_lhs_at<'a>(array: &'a A, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        match indexes.split_first() {
            None => output.push(Self::to_lhs(array)),
            Some((FieldIndex::ArrayIndex(index), rest)) => {
                if let Some(value) = array.get(*index as usize) {
                    value.append_lhs_at(rest, output);
                }
            }
            Some((FieldIndex::MapEach, rest)) => {
                let values = array.iter();
                if rest.is_empty() {
                    output.reserve(values.size_hint().0);
                }
                for value in values {
                    value.append_lhs_at(rest, output);
                }
            }
            Some(_) => panic!("map key used on array"),
        }
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(
        array: &A,
        path: &ArrayPath<<A::Element as ValueType>::Path>,
        predicate: &P,
    ) -> Option<bool> {
        match path {
            ArrayPath::Index(index, child) => {
                let value = array.get(*index as usize)?;
                compare_one(&value, child, predicate)
            }
            ArrayPath::Each(_) => panic!("[*] in scalar comparison path"),
        }
    }

    #[inline]
    fn compare_vec<P: ValuePredicate + ?Sized>(
        array: &A,
        path: &ArrayPath<<A::Element as ValueType>::Path>,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        match path {
            ArrayPath::Index(index, child) => {
                if let Some(value) = array.get(*index as usize) {
                    compare_vec(&value, child, predicate, output);
                }
            }
            ArrayPath::Each(child) => {
                let values = array.iter();
                if A::Element::IS_PRIMITIVE && output.is_empty() {
                    let capacity = values.size_hint().0;
                    if capacity != 0 {
                        *output = TypedArray::with_capacity(capacity);
                    }
                }
                for value in values {
                    compare_vec(&value, child, predicate, output);
                }
            }
        }
    }
}

/// Engine reader for any concrete [`MapValue`] implementation.
pub struct MapRead;

impl<M: MapValue + ?Sized> ReadValue<M, Map<M::Element>> for MapRead {
    fn to_lhs(map: &M) -> LhsValue<'_> {
        let mut entries = Vec::with_capacity(map.values().size_hint().0);
        map.for_each_entry(|key, value| {
            entries.push(Ok::<_, crate::TypeMismatchError>((
                Box::<[u8]>::from(key),
                value.into_lhs(),
            )));
        });
        crate::Map::try_from_iter(M::Element::TYPE, entries)
            .expect("map values must match their declared type")
            .into()
    }

    #[inline]
    fn to_lhs_at<'a>(map: &'a M, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        match indexes.split_first() {
            None => Some(Self::to_lhs(map)),
            Some((FieldIndex::MapKey(key), rest)) => map.get(key.as_bytes())?.into_lhs_at(rest),
            Some(_) => panic!("map selection requires a map key"),
        }
    }

    #[inline]
    fn append_lhs_at<'a>(map: &'a M, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        match indexes.split_first() {
            None => output.push(Self::to_lhs(map)),
            Some((FieldIndex::MapKey(key), rest)) => {
                if let Some(value) = map.get(key.as_bytes()) {
                    value.append_lhs_at(rest, output);
                }
            }
            Some((FieldIndex::MapEach, rest)) => {
                let values = map.values();
                if rest.is_empty() {
                    output.reserve(values.size_hint().0);
                }
                for value in values {
                    value.append_lhs_at(rest, output);
                }
            }
            Some(_) => panic!("array index used on map"),
        }
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(
        map: &M,
        path: &MapPath<<M::Element as ValueType>::Path>,
        predicate: &P,
    ) -> Option<bool> {
        match path {
            MapPath::Key(key, child) => {
                let value = map.get(key)?;
                compare_one(&value, child, predicate)
            }
            MapPath::Each(_) => panic!("[*] in scalar comparison path"),
        }
    }

    #[inline]
    fn compare_vec<P: ValuePredicate + ?Sized>(
        map: &M,
        path: &MapPath<<M::Element as ValueType>::Path>,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        match path {
            MapPath::Key(key, child) => {
                if let Some(value) = map.get(key) {
                    compare_vec(&value, child, predicate, output);
                }
            }
            MapPath::Each(child) => {
                let values = map.values();
                if M::Element::IS_PRIMITIVE && output.is_empty() {
                    let capacity = values.size_hint().0;
                    if capacity != 0 {
                        *output = TypedArray::with_capacity(capacity);
                    }
                }
                for value in values {
                    compare_vec(&value, child, predicate, output);
                }
            }
        }
    }
}

/// Forward a borrowed provider to its concrete engine reader.
pub struct Borrowed<R>(PhantomData<R>);

impl<T: Value + ?Sized> Value for &T {
    type Read = Borrowed<T::Read>;
    type ValueType = T::ValueType;
}

impl<T: Value + ?Sized> ReadValue<&T, T::ValueType> for Borrowed<T::Read> {
    const MATERIALIZES_COLLECTIONS: bool = T::Read::MATERIALIZES_COLLECTIONS;

    #[inline]
    fn to_lhs<'a>(value: &'a &T) -> LhsValue<'a> {
        T::Read::to_lhs(value)
    }

    #[inline]
    fn to_lhs_at<'a>(value: &'a &T, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        T::Read::to_lhs_at(value, indexes)
    }

    #[inline]
    fn append_lhs_at<'a>(value: &'a &T, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        T::Read::append_lhs_at(value, indexes, output);
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(
        value: &&T,
        path: &<T::ValueType as FieldValueType>::Path,
        predicate: &P,
    ) -> Option<bool> {
        compare_one::<T, P>(value, path, predicate)
    }

    #[inline]
    fn compare_vec<P: ValuePredicate + ?Sized>(
        value: &&T,
        path: &<T::ValueType as FieldValueType>::Path,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        compare_vec::<T, P>(value, path, predicate, output);
    }
}

/// Forward boxed storage to its concrete reader.
pub struct BoxRead<R>(PhantomData<R>);

impl<T: Value + ?Sized> Value for Box<T> {
    type Read = BoxRead<T::Read>;
    type ValueType = T::ValueType;
}

impl<'a, T: Value + ?Sized> IntoLhsValue<'a> for Box<T> {
    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        append_stored_lhs_at(self.into_lhs(), indexes, output);
    }
}

impl<T: Value + ?Sized> ReadValue<Box<T>, T::ValueType> for BoxRead<T::Read> {
    const MATERIALIZES_COLLECTIONS: bool = T::Read::MATERIALIZES_COLLECTIONS;

    #[inline]
    fn to_lhs(value: &Box<T>) -> LhsValue<'_> {
        T::Read::to_lhs(value)
    }

    #[inline]
    fn to_lhs_at<'a>(value: &'a Box<T>, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        T::Read::to_lhs_at(value, indexes)
    }

    #[inline]
    fn append_lhs_at<'a>(
        value: &'a Box<T>,
        indexes: &[FieldIndex],
        output: &mut Vec<LhsValue<'a>>,
    ) {
        T::Read::append_lhs_at(value, indexes, output);
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(
        value: &Box<T>,
        path: &<T::ValueType as FieldValueType>::Path,
        predicate: &P,
    ) -> Option<bool> {
        compare_one::<T, P>(value, path, predicate)
    }

    #[inline]
    fn compare_vec<P: ValuePredicate + ?Sized>(
        value: &Box<T>,
        path: &<T::ValueType as FieldValueType>::Path,
        predicate: &P,
        output: &mut TypedArray<'static, bool>,
    ) {
        compare_vec::<T, P>(value, path, predicate, output);
    }
}

impl<T: Value> ArrayValue for Vec<T>
where
    T::ValueType: ValueType,
{
    type Element = T::ValueType;
    type Item<'a>
        = &'a T
    where
        Self: 'a;
    type Iter<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    #[inline]
    fn get(&self, index: usize) -> Option<Self::Item<'_>> {
        self.as_slice().get(index)
    }

    #[inline]
    fn iter(&self) -> Self::Iter<'_> {
        self.as_slice().iter()
    }
}

impl<T: Value> Value for Vec<T>
where
    T::ValueType: ValueType,
{
    type Read = ArrayRead;
    type ValueType = Array<T::ValueType>;
}

impl<'a, T: Value> IntoLhsValue<'a> for Vec<T>
where
    T::ValueType: ValueType,
{
    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        append_stored_lhs_at(self.into_lhs(), indexes, output);
    }
}

impl<T: Value> ArrayValue for [T]
where
    T::ValueType: ValueType,
{
    type Element = T::ValueType;
    type Item<'a>
        = &'a T
    where
        Self: 'a;
    type Iter<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    #[inline]
    fn get(&self, index: usize) -> Option<Self::Item<'_>> {
        <[T]>::get(self, index)
    }

    #[inline]
    fn iter(&self) -> Self::Iter<'_> {
        <[T]>::iter(self)
    }
}

impl<T: Value> Value for [T]
where
    T::ValueType: ValueType,
{
    type Read = ArrayRead;
    type ValueType = Array<T::ValueType>;
}

impl<K: Borrow<[u8]> + Ord, V: Value> MapValue for BTreeMap<K, V>
where
    V::ValueType: ValueType,
{
    type Element = V::ValueType;
    type Item<'a>
        = &'a V
    where
        Self: 'a;
    type Iter<'a>
        = std::collections::btree_map::Values<'a, K, V>
    where
        Self: 'a;

    #[inline]
    fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
        BTreeMap::get(self, key)
    }

    #[inline]
    fn values(&self) -> Self::Iter<'_> {
        BTreeMap::values(self)
    }

    #[inline]
    fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(&[u8], Self::Item<'a>)) {
        for (key, value) in self {
            visitor(key.borrow(), value);
        }
    }
}

impl<K: Borrow<[u8]> + Ord, V: Value> Value for BTreeMap<K, V>
where
    V::ValueType: ValueType,
{
    type Read = MapRead;
    type ValueType = Map<V::ValueType>;
}

impl<'a, K: Borrow<[u8]> + Ord, V: Value> IntoLhsValue<'a> for BTreeMap<K, V>
where
    V::ValueType: ValueType,
{
    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        append_stored_lhs_at(self.into_lhs(), indexes, output);
    }
}

/// A small borrowed selection descriptor that can be returned by value.
#[derive(Debug, Clone, Copy)]
pub struct SliceView<'a, T>(pub &'a [T]);

impl<T: Value> ArrayValue for SliceView<'_, T>
where
    T::ValueType: ValueType,
{
    type Element = T::ValueType;
    type Item<'a>
        = &'a T
    where
        Self: 'a;
    type Iter<'a>
        = std::slice::Iter<'a, T>
    where
        Self: 'a;

    #[inline]
    fn get(&self, index: usize) -> Option<Self::Item<'_>> {
        self.0.get(index)
    }

    #[inline]
    fn iter(&self) -> Self::Iter<'_> {
        self.0.iter()
    }
}

impl<T: Value> Value for SliceView<'_, T>
where
    T::ValueType: ValueType,
{
    type Read = ArrayRead;
    type ValueType = Array<T::ValueType>;
}

impl<'a, 'data: 'a, T: Value> IntoLhsValue<'a> for SliceView<'data, T>
where
    T::ValueType: ValueType,
{
    fn into_lhs(self) -> LhsValue<'a> {
        ArrayRead::to_lhs(self.0)
    }

    #[inline]
    fn into_lhs_at(self, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
        self.0.into_lhs_at(indexes)
    }

    #[inline]
    fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
        self.0.append_lhs_at(indexes, output);
    }
}

/// Byte-string type; storage can be any concrete byte-slice provider.
pub struct Bytes;
/// Engine reader for a provider implementing `AsRef<[u8]>`.
pub struct BytesRead;

fn validate_scalar_path(
    path: &[FieldIndex],
    input_type: Type,
    scalar_type: Type,
) -> Result<(), ValueError> {
    if !path.is_empty() {
        Err(ValueError("path continues beyond scalar"))
    } else if input_type != scalar_type {
        Err(ValueError(
            "predicate input type differs from selected scalar",
        ))
    } else {
        Ok(())
    }
}

impl ValueType for Bytes {
    type Path = ();

    const IS_PRIMITIVE: bool = true;
    const TYPE: Type = Type::Bytes;

    fn compile_path(path: &[FieldIndex], input_type: Type) -> Result<Self::Path, ValueError> {
        validate_scalar_path(path, input_type, Type::Bytes)
    }
}

impl<T: AsRef<[u8]> + ?Sized> ReadValue<T, Bytes> for BytesRead {
    #[inline]
    fn to_lhs(value: &T) -> LhsValue<'_> {
        value.as_ref().into()
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(value: &T, _: &(), predicate: &P) -> Option<bool> {
        Some(predicate.bytes(value.as_ref()))
    }
}

macro_rules! bytes_storage {
    ($($ty:ty),* $(,)?) => {$(
        impl Value for $ty {
            type ValueType = Bytes;
            type Read = BytesRead;
        }
    )*};
}

// `u8` deliberately has no Value implementation: Vec<u8> and [u8] are
// byte strings, while Vec<T> and [T] compose arrays for element types implementing Value.
bytes_storage!(str, String, [u8], Vec<u8>, Cow<'_, [u8]>);

#[cfg(feature = "bytes")]
bytes_storage!(bytes::Bytes);

impl IntoLhsValue<'_> for String {}
impl IntoLhsValue<'_> for Vec<u8> {}

#[cfg(feature = "bytes")]
impl IntoLhsValue<'_> for bytes::Bytes {}

impl<'a, 'data: 'a> IntoLhsValue<'a> for Cow<'data, [u8]> {
    #[inline]
    fn into_lhs(self) -> LhsValue<'a> {
        LhsValue::Bytes(crate::Bytes::from(self))
    }
}

macro_rules! ordered_scalar {
    ($marker:ident, $ty:ty, $variant:ident, $compare:ident, $doc:literal) => {
        #[doc = $doc]
        pub struct $marker;
        impl ValueType for $marker {
            type Path = ();

            const IS_PRIMITIVE: bool = true;
            const TYPE: Type = Type::$variant;

            fn compile_path(
                path: &[FieldIndex],
                input_type: Type,
            ) -> Result<Self::Path, ValueError> {
                validate_scalar_path(path, input_type, Type::$variant)
            }
        }
        impl Value for $ty {
            type Read = $marker;
            type ValueType = $marker;
        }
        impl ReadValue<$ty, $marker> for $marker {
            #[inline]
            fn to_lhs(value: &$ty) -> LhsValue<'_> {
                LhsValue::$variant(*value)
            }

            #[inline]
            fn compare_one<P: ValuePredicate + ?Sized>(
                value: &$ty,
                _: &(),
                predicate: &P,
            ) -> Option<bool> {
                Some(predicate.$compare(*value))
            }
        }
        impl IntoLhsValue<'_> for $ty {}
    };
}

ordered_scalar!(Int, i64, Int, int, "Integer type and its engine reader.");
ordered_scalar!(Ip, IpAddr, Ip, ip, "IP-address type and its engine reader.");

/// Boolean type and reader for direct boolean evaluation.
pub struct Bool;

impl ValueType for Bool {
    type Path = ();

    const IS_PRIMITIVE: bool = true;
    const TYPE: Type = Type::Bool;

    fn compile_path(path: &[FieldIndex], input_type: Type) -> Result<Self::Path, ValueError> {
        validate_scalar_path(path, input_type, Type::Bool)
    }
}

impl Value for bool {
    type Read = Bool;
    type ValueType = Bool;
}

impl ReadValue<bool, Bool> for Bool {
    #[inline]
    fn to_lhs(value: &bool) -> LhsValue<'_> {
        LhsValue::Bool(*value)
    }

    #[inline]
    fn compare_one<P: ValuePredicate + ?Sized>(
        value: &bool,
        _: &(),
        predicate: &P,
    ) -> Option<bool> {
        Some(predicate.boolean(*value))
    }
}

impl IntoLhsValue<'_> for bool {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    fn bytes<'a>(value: &'a LhsValue<'_>) -> &'a [u8] {
        match value {
            LhsValue::Bytes(value) => value.as_ref(),
            _ => panic!("expected bytes"),
        }
    }

    #[test]
    fn test_bytes_materialization_preserves_payload_storage() {
        let input = vec![0xff, b'a'];
        let borrowed = crate::Bytes::Borrowed(&input).into_lhs();
        assert_eq!(bytes(&borrowed).as_ptr(), input.as_ptr());
        assert!(matches!(
            borrowed,
            LhsValue::Bytes(crate::Bytes::Borrowed(_))
        ));

        let input = input.into_boxed_slice();
        let ptr = input.as_ptr();
        let owned = crate::Bytes::Owned(input).into_lhs();
        assert_eq!(bytes(&owned).as_ptr(), ptr);
        assert!(matches!(owned, LhsValue::Bytes(crate::Bytes::Owned(_))));

        let source = vec![
            crate::Bytes::Borrowed(b"borrowed"),
            crate::Bytes::from("owned".to_owned()),
        ];
        let LhsValue::Array(array) = (&source).into_lhs() else {
            panic!("expected an array");
        };
        for (index, original) in source.iter().enumerate() {
            let value = array.get(index).unwrap();
            assert_eq!(bytes(value), original.as_ref());
            assert_eq!(bytes(value).as_ptr(), original.as_ref().as_ptr());
            assert!(matches!(value, LhsValue::Bytes(crate::Bytes::Borrowed(_))));
        }
    }

    #[test]
    fn test_cow_materialization_preserves_ownership() {
        let input = vec![0xff, b'a'];
        let borrowed = Cow::Borrowed(input.as_slice()).into_lhs();
        assert_eq!(bytes(&borrowed).as_ptr(), input.as_ptr());

        let owned: LhsValue<'static> = Cow::<'_, [u8]>::Owned(input).into_lhs();
        assert_eq!(bytes(&owned), &[0xff, b'a']);
        assert!(matches!(owned, LhsValue::Bytes(crate::Bytes::Owned(_))));
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_materialization_borrows_or_copies_as_needed() {
        let input = bytes::Bytes::from(vec![0xff, b'a']);
        let borrowed = (&input).into_lhs();
        assert_eq!(bytes(&borrowed).as_ptr(), input.as_ptr());
        assert!(matches!(
            borrowed,
            LhsValue::Bytes(crate::Bytes::Borrowed(_))
        ));

        // LhsValue has no shared ownership variant, so consuming the last owner
        // requires an owned copy. Borrowed field getters avoid this copy.
        let owned: LhsValue<'static> = input.into_lhs();
        assert_eq!(bytes(&owned), &[0xff, b'a']);
        assert!(matches!(owned, LhsValue::Bytes(crate::Bytes::Owned(_))));
    }

    #[test]
    fn test_nested_materialization_preserves_types_and_borrows_payloads() {
        let source = BTreeMap::from([(
            Box::<[u8]>::from(&b"Mixed\xff"[..]),
            vec![Box::<str>::from("first"), Box::<str>::from("second")].into_boxed_slice(),
        )]);
        let value = (&source).into_lhs();
        let LhsValue::Map(map) = value else {
            panic!("expected a map")
        };
        assert_eq!(map.value_type(), Type::array(Type::Bytes));
        assert!(map.get(b"mixed\xff").is_none());
        let LhsValue::Array(array) = map.get(b"Mixed\xff").unwrap() else {
            panic!("expected an array")
        };
        assert_eq!(array.value_type(), Type::Bytes);
        let source_values = source.get(&b"Mixed\xff"[..]).unwrap();
        for (index, text) in source_values.iter().enumerate() {
            let actual = bytes(array.get(index).unwrap());
            assert_eq!(actual, text.as_bytes());
            assert_eq!(actual.as_ptr(), text.as_ptr());
        }

        let empty: Vec<BTreeMap<Box<[u8]>, Vec<i64>>> = Vec::new();
        let LhsValue::Array(array) = (&empty).into_lhs() else {
            panic!("expected an array")
        };
        assert_eq!(array.value_type(), Type::map(Type::array(Type::Int)));
        assert!(array.is_empty());
    }

    struct SelectionMap(Vec<String>);

    impl Value for SelectionMap {
        type Read = MapRead;
        type ValueType = Map<Array<Bytes>>;
    }

    impl MapValue for SelectionMap {
        type Element = Array<Bytes>;
        type Item<'a> = SliceView<'a, String>;
        type Iter<'a> = std::iter::Once<SliceView<'a, String>>;

        fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
            (key == b"accept").then_some(SliceView(&self.0))
        }

        fn values(&self) -> Self::Iter<'_> {
            std::iter::once(SliceView(&self.0))
        }

        fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(&[u8], Self::Item<'a>)) {
            visitor(b"accept", SliceView(&self.0));
        }
    }

    #[test]
    fn test_temporary_array_selection_can_preserve_borrowed_payloads() {
        let source = SelectionMap(vec!["text/html".into()]);
        // The selection descriptor is consumed here; only its payload outlives it.
        let selected = source.get(b"accept").unwrap().into_lhs();
        let LhsValue::Array(array) = selected else {
            panic!("expected an array")
        };
        assert_eq!(bytes(array.get(0).unwrap()).as_ptr(), source.0[0].as_ptr());

        let LhsValue::Map(map) = (&source).into_lhs() else {
            panic!("expected a map")
        };
        let LhsValue::Array(array) = map.get(b"accept").unwrap() else {
            panic!("expected an array")
        };
        assert_eq!(bytes(array.get(0).unwrap()).as_ptr(), source.0[0].as_ptr());
    }

    #[test]
    fn test_indexed_materialization_preserves_borrowed_descriptors() {
        let source = Box::new(SelectionMap(vec!["text/html".into()]));
        let reference = &source;
        let indexes = [
            FieldIndex::MapKey("accept".into()),
            FieldIndex::ArrayIndex(0),
        ];
        // The map creates a temporary SliceView. Its consuming conversion must
        // retain the source lifetime through both indexes and reader wrappers.
        for selected in [
            reference.into_lhs_at(&indexes).unwrap(),
            (&reference).into_lhs_at(&indexes).unwrap(),
            SliceView(source.0.as_slice())
                .into_lhs_at(&indexes[1..])
                .unwrap(),
        ] {
            assert!(matches!(
                selected,
                LhsValue::Bytes(crate::Bytes::Borrowed(_))
            ));
            assert_eq!(bytes(&selected).as_ptr(), source.0[0].as_ptr());
        }
        assert!(
            reference
                .into_lhs_at(&[FieldIndex::MapKey("missing".into())])
                .is_none()
        );
        assert!(
            reference
                .into_lhs_at(&[
                    FieldIndex::MapKey("accept".into()),
                    FieldIndex::ArrayIndex(1),
                ])
                .is_none()
        );
    }

    #[test]
    fn test_map_each_materialization_preserves_borrowed_descriptors() {
        let source = Box::new(SelectionMap(vec!["text/html".into(), "text/plain".into()]));
        let reference = &source;
        for indexes in [
            vec![FieldIndex::MapEach, FieldIndex::MapEach],
            vec![FieldIndex::MapKey("accept".into()), FieldIndex::MapEach],
        ] {
            // Each map item is a temporary SliceView, consumed during traversal.
            // Both wrapper readers must preserve its references to the source.
            let mut actual = vec![LhsValue::Bool(true)];
            reference.append_lhs_at(&indexes, &mut actual);
            (&reference).append_lhs_at(&indexes, &mut actual);
            assert_eq!(actual[0], LhsValue::Bool(true));
            assert_eq!(actual.len(), 5);
            for (value, original) in actual[1..].iter().zip(source.0.iter().cycle()) {
                assert!(matches!(value, LhsValue::Bytes(crate::Bytes::Borrowed(_))));
                assert_eq!(bytes(value).as_ptr(), original.as_ptr());
            }
        }

        let mut selected = Vec::new();
        reference.append_lhs_at(
            &[FieldIndex::MapEach, FieldIndex::ArrayIndex(1)],
            &mut selected,
        );
        assert_eq!(selected.len(), 1);
        assert_eq!(bytes(&selected[0]).as_ptr(), source.0[1].as_ptr());
        for indexes in [
            vec![FieldIndex::MapEach, FieldIndex::ArrayIndex(99)],
            vec![FieldIndex::MapKey("missing".into()), FieldIndex::MapEach],
        ] {
            reference.append_lhs_at(&indexes, &mut selected);
            assert_eq!(selected.len(), 1);
        }

        // Stopping at a container preserves that container, rather than
        // flattening beyond the specified `[*]`.
        let mut containers = Vec::new();
        reference.append_lhs_at(&[FieldIndex::MapEach], &mut containers);
        assert_eq!(containers.len(), 1);
        let LhsValue::Array(array) = &containers[0] else {
            panic!("expected the selected array");
        };
        assert_eq!(array.len(), 2);
        assert_eq!(bytes(array.get(0).unwrap()).as_ptr(), source.0[0].as_ptr());
    }

    #[test]
    fn test_indexed_descriptor_fallback_preserves_custom_conversion() {
        struct Descriptor<'a> {
            values: &'a [String],
            conversions: &'a Cell<usize>,
        }
        impl Value for Descriptor<'_> {
            type Read = ArrayRead;
            type ValueType = Array<Bytes>;
        }
        impl ArrayValue for Descriptor<'_> {
            type Element = Bytes;
            type Item<'a>
                = &'a String
            where
                Self: 'a;
            type Iter<'a>
                = std::slice::Iter<'a, String>
            where
                Self: 'a;

            fn get(&self, index: usize) -> Option<Self::Item<'_>> {
                self.values.get(index)
            }

            fn iter(&self) -> Self::Iter<'_> {
                self.values.iter()
            }
        }
        impl<'a> IntoLhsValue<'a> for Descriptor<'a> {
            fn into_lhs(self) -> LhsValue<'a> {
                self.conversions.set(self.conversions.get() + 1);
                self.values.into_lhs()
            }
        }

        let values = vec!["borrowed".to_owned()];
        let conversions = Cell::new(0);
        let selected = Descriptor {
            values: &values,
            conversions: &conversions,
        }
        .into_lhs_at(&[FieldIndex::ArrayIndex(0)])
        .unwrap();
        assert_eq!(conversions.get(), 1);
        assert!(matches!(
            selected,
            LhsValue::Bytes(crate::Bytes::Borrowed(_))
        ));
        assert_eq!(bytes(&selected).as_ptr(), values[0].as_ptr());

        let mut flattened = Vec::new();
        Descriptor {
            values: &values,
            conversions: &conversions,
        }
        .append_lhs_at(&[FieldIndex::MapEach], &mut flattened);
        assert_eq!(conversions.get(), 2);
        assert_eq!(flattened.len(), 1);
        assert!(matches!(
            flattened[0],
            LhsValue::Bytes(crate::Bytes::Borrowed(_))
        ));
        assert_eq!(bytes(&flattened[0]).as_ptr(), values[0].as_ptr());

        // The same fallback must also remain safe for a temporary owning its
        // payload: after it is consumed, the selected result owns its bytes.
        let selected: LhsValue<'static> = vec!["owned".to_owned()]
            .into_lhs_at(&[FieldIndex::ArrayIndex(0)])
            .unwrap();
        assert!(matches!(selected, LhsValue::Bytes(crate::Bytes::Owned(_))));
        assert_eq!(bytes(&selected), b"owned");

        let mut flattened: Vec<LhsValue<'static>> = Vec::new();
        vec![vec!["owned".to_owned()], vec![]].append_lhs_at(
            &[FieldIndex::MapEach, FieldIndex::ArrayIndex(0)],
            &mut flattened,
        );
        assert_eq!(flattened.len(), 1);
        assert!(matches!(
            flattened[0],
            LhsValue::Bytes(crate::Bytes::Owned(_))
        ));
        assert_eq!(bytes(&flattened[0]), b"owned");
    }

    #[test]
    fn test_map_each_fallback_preserves_custom_indexed_conversion() {
        struct IndexedSelection<'a>(&'a [Vec<String>]);

        impl Value for IndexedSelection<'_> {
            type Read = ArrayRead;
            type ValueType = Array<Array<Bytes>>;
        }

        impl ArrayValue for IndexedSelection<'_> {
            type Element = Array<Bytes>;
            type Item<'a>
                = &'a Vec<String>
            where
                Self: 'a;
            type Iter<'a>
                = std::slice::Iter<'a, Vec<String>>
            where
                Self: 'a;

            fn get(&self, index: usize) -> Option<Self::Item<'_>> {
                self.0.get(index)
            }

            fn iter(&self) -> Self::Iter<'_> {
                self.0.iter()
            }
        }

        impl<'a> IntoLhsValue<'a> for IndexedSelection<'a> {
            fn into_lhs(self) -> LhsValue<'a> {
                panic!("the custom indexed conversion must be used");
            }

            fn into_lhs_at(self, indexes: &[FieldIndex]) -> Option<LhsValue<'a>> {
                self.0.into_lhs_at(indexes)
            }
        }

        let source = vec![vec!["first".to_owned(), "second".to_owned()]];
        let mut selected = Vec::new();
        IndexedSelection(&source).append_lhs_at(
            &[FieldIndex::ArrayIndex(0), FieldIndex::MapEach],
            &mut selected,
        );
        assert_eq!(selected.len(), 2);
        for (value, original) in selected.iter().zip(&source[0]) {
            assert!(matches!(value, LhsValue::Bytes(crate::Bytes::Borrowed(_))));
            assert_eq!(bytes(value).as_ptr(), original.as_ptr());
        }
    }

    #[test]
    fn test_map_each_preserves_custom_child_append() {
        struct AppendingSelection<'a>(&'a [String]);

        impl Value for AppendingSelection<'_> {
            type Read = ArrayRead;
            type ValueType = Array<Bytes>;
        }

        impl ArrayValue for AppendingSelection<'_> {
            type Element = Bytes;
            type Item<'a>
                = &'a String
            where
                Self: 'a;
            type Iter<'a>
                = std::slice::Iter<'a, String>
            where
                Self: 'a;

            fn get(&self, _: usize) -> Option<Self::Item<'_>> {
                panic!("the custom append method must be used");
            }

            fn iter(&self) -> Self::Iter<'_> {
                panic!("the custom append method must be used");
            }
        }

        impl<'a> IntoLhsValue<'a> for AppendingSelection<'a> {
            fn into_lhs(self) -> LhsValue<'a> {
                panic!("the custom append method must be used");
            }

            fn into_lhs_at(self, _: &[FieldIndex]) -> Option<LhsValue<'a>> {
                panic!("the custom append method must be used");
            }

            fn append_lhs_at(self, indexes: &[FieldIndex], output: &mut Vec<LhsValue<'a>>) {
                assert_eq!(indexes, &[FieldIndex::ArrayIndex(0)]);
                self.0.append_lhs_at(indexes, output);
            }
        }

        struct MapWithSelection(Vec<String>);

        impl Value for MapWithSelection {
            type Read = MapRead;
            type ValueType = Map<Array<Bytes>>;
        }

        impl MapValue for MapWithSelection {
            type Element = Array<Bytes>;
            type Item<'a> = AppendingSelection<'a>;
            type Iter<'a> = std::iter::Once<AppendingSelection<'a>>;

            fn get(&self, key: &[u8]) -> Option<Self::Item<'_>> {
                (key == b"values").then_some(AppendingSelection(&self.0))
            }

            fn values(&self) -> Self::Iter<'_> {
                std::iter::once(AppendingSelection(&self.0))
            }

            fn for_each_entry<'a>(&'a self, mut visitor: impl FnMut(&[u8], Self::Item<'a>)) {
                visitor(b"values", AppendingSelection(&self.0));
            }
        }

        let source = MapWithSelection(vec!["selected".to_owned(), "other".to_owned()]);
        let mut selected = vec![LhsValue::Bool(true)];
        (&source).append_lhs_at(
            &[FieldIndex::MapEach, FieldIndex::ArrayIndex(0)],
            &mut selected,
        );
        assert_eq!(selected.len(), 2);
        assert_eq!(selected[0], LhsValue::Bool(true));
        assert!(matches!(
            selected[1],
            LhsValue::Bytes(crate::Bytes::Borrowed(_))
        ));
        assert_eq!(bytes(&selected[1]).as_ptr(), source.0[0].as_ptr());
    }

    #[test]
    fn test_owned_containers_append_selected_values_with_owned_payloads() {
        fn check(value: impl IntoLhsValue<'static>, indexes: &[FieldIndex]) {
            let mut selected = vec![LhsValue::Bool(true)];
            value.append_lhs_at(indexes, &mut selected);
            assert_eq!(selected.len(), 2);
            assert_eq!(selected[0], LhsValue::Bool(true));
            assert!(matches!(
                selected[1],
                LhsValue::Bytes(crate::Bytes::Owned(_))
            ));
            assert_eq!(bytes(&selected[1]), b"selected");
        }

        let rows = vec![vec!["selected".to_owned()], vec![]];
        check(
            vec![vec![vec!["other".to_owned()]], rows.clone()],
            &[
                FieldIndex::ArrayIndex(1),
                FieldIndex::MapEach,
                FieldIndex::ArrayIndex(0),
            ],
        );
        check(
            Box::new(rows.clone()),
            &[FieldIndex::MapEach, FieldIndex::ArrayIndex(0)],
        );
        check(
            BTreeMap::from([
                (Box::<[u8]>::from(&b"wanted"[..]), rows),
                (
                    Box::<[u8]>::from(&b"other"[..]),
                    vec![vec!["other".to_owned()]],
                ),
            ]),
            &[
                FieldIndex::MapKey("wanted".into()),
                FieldIndex::MapEach,
                FieldIndex::ArrayIndex(0),
            ],
        );
    }

    #[test]
    fn test_default_descriptor_conversion_owns_temporary_payload() {
        struct Temporary(Box<[u8]>);

        impl AsRef<[u8]> for Temporary {
            fn as_ref(&self) -> &[u8] {
                &self.0
            }
        }

        impl Value for Temporary {
            type Read = BytesRead;
            type ValueType = Bytes;
        }

        impl IntoLhsValue<'_> for Temporary {}

        let result: LhsValue<'static> = Temporary(Box::from(&b"temporary"[..])).into_lhs();
        assert_eq!(bytes(&result), b"temporary");
    }

    #[test]
    fn test_owned_primitive_and_collection_conversion() {
        assert_eq!(42i64.into_lhs(), LhsValue::Int(42));
        assert_eq!(true.into_lhs(), LhsValue::Bool(true));
        let ip = IpAddr::V4(std::net::Ipv4Addr::LOCALHOST);
        assert_eq!(ip.into_lhs(), LhsValue::Ip(ip));
        let value: LhsValue<'static> = vec!["one".to_owned()].into_lhs();
        let LhsValue::Array(array) = value else {
            panic!("expected an array")
        };
        assert_eq!(bytes(array.get(0).unwrap()), b"one");
    }

    struct Matches<'a> {
        needle: &'a [u8],
        reads: &'a Cell<usize>,
    }

    impl ValuePredicate for Matches<'_> {
        fn bytes(&self, value: &[u8]) -> bool {
            self.reads.set(self.reads.get() + 1);
            value == self.needle
        }
    }

    #[test]
    fn test_scalar_comparison_distinguishes_false_from_missing() {
        type Input = Box<Vec<BTreeMap<Box<[u8]>, Vec<String>>>>;
        let input: Input = Box::new(vec![BTreeMap::from([(
            Box::from(b"key".as_slice()),
            vec!["miss".into(), "hit".into()],
        )])]);
        let reads = Cell::new(0);
        let predicate = Matches {
            needle: b"hit",
            reads: &reads,
        };
        // Exercise both reference and Box forwarding through nested selections.
        for (outer, key, inner, expected) in [
            (0, "key", 0, Some(false)),
            (0, "key", 1, Some(true)),
            (0, "key", 2, None),
            (0, "absent", 0, None),
            (1, "key", 0, None),
            (u32::MAX, "key", 0, None),
            (0, "key", u32::MAX, None),
        ] {
            let path = <Input as Value>::ValueType::compile_path(
                &[
                    FieldIndex::ArrayIndex(outer),
                    FieldIndex::MapKey(key.into()),
                    FieldIndex::ArrayIndex(inner),
                ],
                Type::Bytes,
            )
            .unwrap();
            assert_eq!(compare_one(&&input, &path, &predicate), expected);
        }
        assert_eq!(reads.get(), 2);
    }

    #[test]
    fn test_array_comparison_appends_in_map_order() {
        type Input = Box<BTreeMap<Box<[u8]>, Vec<String>>>;
        let input: Input = Box::new(BTreeMap::from([
            (Box::from(b"c".as_slice()), vec!["hit".into()]),
            (
                Box::from(b"a".as_slice()),
                vec!["miss".into(), "hit".into()],
            ),
            (Box::from(b"b".as_slice()), vec![]),
        ]));
        let reads = Cell::new(0);
        let predicate = Matches {
            needle: b"hit",
            reads: &reads,
        };
        let path = <Input as Value>::ValueType::compile_path(
            &[FieldIndex::MapEach, FieldIndex::MapEach],
            Type::Bytes,
        )
        .unwrap();
        let mut output = TypedArray::from_iter([true]);
        compare_vec(&&input, &path, &predicate, &mut output);
        assert_eq!(output, [true, false, true, true]);
        assert_eq!(reads.get(), 3);

        // Scalar-valued maps also append without replacing earlier results.
        let values = BTreeMap::from([(Box::<[u8]>::from(b"a".as_slice()), "miss".to_owned())]);
        let path = Map::<Bytes>::compile_path(&[FieldIndex::MapEach], Type::Bytes).unwrap();
        compare_vec(&values, &path, &predicate, &mut output);
        assert_eq!(output, [true, false, true, true, false]);
        assert_eq!(reads.get(), 4);
    }

    #[test]
    #[should_panic(expected = "[*] in scalar comparison path")]
    fn test_scalar_array_comparison_rejects_map_each() {
        let path = Array::<Bytes>::compile_path(&[FieldIndex::MapEach], Type::Bytes).unwrap();
        compare_one(
            &Vec::<String>::new(),
            &path,
            &Matches {
                needle: b"hit",
                reads: &Cell::new(0),
            },
        );
    }

    #[test]
    #[should_panic(expected = "[*] in scalar comparison path")]
    fn test_scalar_map_comparison_rejects_map_each() {
        let path = Map::<Bytes>::compile_path(&[FieldIndex::MapEach], Type::Bytes).unwrap();
        compare_one(
            &BTreeMap::<Box<[u8]>, String>::new(),
            &path,
            &Matches {
                needle: b"hit",
                reads: &Cell::new(0),
            },
        );
    }

    #[test]
    fn test_custom_predicate_traverses_nested_projections_without_missing_values() {
        type Input = Vec<BTreeMap<Box<[u8]>, Vec<String>>>;
        let key = Box::<[u8]>::from(&b"key"[..]);
        let input: Input = vec![
            BTreeMap::from([(key.clone(), vec!["one".into(), "two".into()])]),
            BTreeMap::new(),
            BTreeMap::from([(key, vec!["two".into()])]),
        ];
        let reads = Cell::new(0);
        let predicate = Matches {
            needle: b"two",
            reads: &reads,
        };
        let path = <Input as Value>::ValueType::compile_path(
            &[
                FieldIndex::MapEach,
                FieldIndex::MapKey("key".into()),
                FieldIndex::MapEach,
            ],
            Type::Bytes,
        )
        .unwrap();
        let mut results = TypedArray::new();
        compare_vec(&input, &path, &predicate, &mut results);
        assert_eq!(results, [false, true, true]);
        assert_eq!(reads.get(), 3);

        let absent = <Input as Value>::ValueType::compile_path(
            &[
                FieldIndex::ArrayIndex(8),
                FieldIndex::MapKey("key".into()),
                FieldIndex::ArrayIndex(0),
            ],
            Type::Bytes,
        )
        .unwrap();
        assert_eq!(compare_one(&input, &absent, &predicate), None);
        assert_eq!(reads.get(), 3);

        for indexes in [
            [
                FieldIndex::ArrayIndex(u32::MAX),
                FieldIndex::MapKey("key".into()),
                FieldIndex::MapEach,
            ],
            [
                FieldIndex::MapEach,
                FieldIndex::MapKey("key".into()),
                FieldIndex::ArrayIndex(u32::MAX),
            ],
        ] {
            let path = <Input as Value>::ValueType::compile_path(&indexes, Type::Bytes).unwrap();
            compare_vec(&input, &path, &predicate, &mut results);
            assert_eq!(results, [false, true, true]);
            assert_eq!(reads.get(), 3);
        }
    }

    #[test]
    fn test_custom_predicate_path_validates_value_type() {
        type Nested = Array<Map<Array<Bytes>>>;
        let path = [
            FieldIndex::MapEach,
            FieldIndex::MapKey("key".into()),
            FieldIndex::MapEach,
        ];
        assert!(Nested::compile_path(&path, Type::Bytes).is_ok());
        assert!(Nested::compile_path(&path, Type::Int).is_err());
        assert!(Nested::compile_path(&path[..2], Type::Bytes).is_err());
        assert!(
            Array::<Int>::compile_path(&[FieldIndex::MapKey("key".into())], Type::Int).is_err()
        );
        assert!(Map::<Int>::compile_path(&[FieldIndex::ArrayIndex(0)], Type::Int).is_err());
        assert!(Int::compile_path(&[FieldIndex::MapEach], Type::Int).is_err());
        assert!(Int::compile_path(&[], Type::Int).is_ok());
        assert!(Ip::compile_path(&[], Type::Ip).is_ok());
        assert!(Bool::compile_path(&[], Type::Bool).is_ok());
        assert!(Bytes::compile_path(&[], Type::array(Type::Bytes)).is_err());
    }

    #[test]
    fn test_custom_predicate_receives_each_scalar_kind() {
        struct IntPredicate;
        impl ValuePredicate for IntPredicate {
            fn int(&self, value: i64) -> bool {
                value == 42
            }
        }
        struct IpPredicate;
        impl ValuePredicate for IpPredicate {
            fn ip(&self, value: IpAddr) -> bool {
                value.is_loopback()
            }
        }
        struct BoolPredicate;
        impl ValuePredicate for BoolPredicate {
            fn boolean(&self, value: bool) -> bool {
                !value
            }
        }
        let mut results = TypedArray::new();
        compare_vec(&42i64, &(), &IntPredicate, &mut results);
        compare_vec(
            &IpAddr::V4(std::net::Ipv4Addr::LOCALHOST),
            &(),
            &IpPredicate,
            &mut results,
        );
        compare_vec(&false, &(), &BoolPredicate, &mut results);
        assert_eq!(results, [true, true, true]);
    }
}
