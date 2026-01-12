use super::{TypedMap, map::InnerMap};
use crate::types::{
    CompoundType, GetType, IntoValue, LhsValue, LhsValueSeed, Type, TypeMismatchError,
};
use dyn_hash::DynHash;
use serde::{
    Serialize, Serializer,
    de::{self, DeserializeSeed, Deserializer, SeqAccess, Visitor},
    ser::SerializeSeq,
};
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::sync::Arc;
use std::{
    fmt,
    hash::{Hash, Hasher},
    hint::unreachable_unchecked,
};

type IterFn<'a> = fn(NonNull<u8>) -> Option<LhsValue<'a>>;

pub(crate) struct Iter<'slice> {
    ptr: NonNull<u8>,
    size: usize,
    len: usize,
    func: IterFn<'slice>,
    _marker: PhantomData<LhsValue<'slice>>,
}

impl<'slice> Iter<'slice> {
    fn new<T>(s: &'slice [T]) -> Iter<'slice>
    where
        &'slice T: ArrayIntoValue<'slice>,
    {
        let ptr = NonNull::from_ref(s).cast();
        Self {
            ptr,
            size: std::mem::size_of::<T>(),
            len: s.len(),
            func: |ptr| {
                Some({
                    let val: &'slice T = unsafe { ptr.cast::<T>().as_ref() };
                    val.into_value()
                })
            },
            _marker: PhantomData,
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<LhsValue<'a>> {
        if self.len == 0 {
            None
        } else {
            let value = (self.func)(self.ptr);
            self.ptr = unsafe { self.ptr.add(self.size) };
            self.len -= 1;
            value
        }
    }
}

pub(crate) trait ArraySlice: std::fmt::Debug + DynHash + Send + Sync {
    fn len(&self) -> usize;

    fn is_empty(&self) -> bool;

    fn get(&self, idx: usize) -> Option<LhsValue<'_>>;

    fn iter(&self) -> Iter<'_>;

    fn eq_slice(&self, slice: &[LhsValue<'_>]) -> bool;
}

dyn_hash::hash_trait_object!(ArraySlice);

trait ArrayIntoValue<'a> {
    fn into_value(self) -> LhsValue<'a>;
}

impl<'a, T: IntoValue<'a>> ArrayIntoValue<'a> for T {
    #[inline(always)]
    fn into_value(self) -> LhsValue<'a> {
        IntoValue::into_value(self)
    }
}

impl<'a> ArrayIntoValue<'a> for &'a LhsValue<'a> {
    #[inline(always)]
    fn into_value(self) -> LhsValue<'a> {
        self.as_ref()
    }
}

impl<'a> ArraySlice for Vec<LhsValue<'a>> {
    fn len(&self) -> usize {
        (*self).len()
    }

    fn is_empty(&self) -> bool {
        (*self).is_empty()
    }

    fn get(&self, idx: usize) -> Option<LhsValue<'_>> {
        (**self).get(idx).map(LhsValue::as_ref)
    }

    fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }

    fn eq_slice(&self, slice: &[LhsValue<'_>]) -> bool {
        self == slice
    }
}

impl<T: std::fmt::Debug + Hash + Send + Sync> ArraySlice for Vec<T>
where
    for<'b> &'b T: IntoValue<'b>,
{
    fn len(&self) -> usize {
        (**self).len()
    }

    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }

    fn get(&self, idx: usize) -> Option<LhsValue<'_>> {
        (**self).get(idx).map(IntoValue::into_value)
    }

    fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }

    fn eq_slice(&self, slice: &[LhsValue<'_>]) -> bool {
        (**self).iter().map(IntoValue::into_value).eq(slice.iter())
    }
}

impl<T: std::fmt::Debug + Hash + Send + Sync> ArraySlice for Box<[T]>
where
    for<'b> &'b T: IntoValue<'b>,
{
    fn len(&self) -> usize {
        (**self).len()
    }

    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }

    fn get(&self, idx: usize) -> Option<LhsValue<'_>> {
        (**self).get(idx).map(IntoValue::into_value)
    }

    fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }

    fn eq_slice(&self, slice: &[LhsValue<'_>]) -> bool {
        (**self).iter().map(IntoValue::into_value).eq(slice.iter())
    }
}

impl<T: std::fmt::Debug + Hash + Send + Sync> ArraySlice for Arc<[T]>
where
    for<'b> &'b T: IntoValue<'b>,
{
    fn len(&self) -> usize {
        (**self).len()
    }

    fn is_empty(&self) -> bool {
        (**self).is_empty()
    }

    fn get(&self, idx: usize) -> Option<LhsValue<'_>> {
        (**self).get(idx).map(IntoValue::into_value)
    }

    fn iter(&self) -> Iter<'_> {
        Iter::new(self)
    }

    fn eq_slice(&self, slice: &[LhsValue<'_>]) -> bool {
        (**self).iter().map(IntoValue::into_value).eq(slice.iter())
    }
}

// Ideally, we would want to use Cow<'a, LhsValue<'a>> here
// but it doesnt work for unknown reasons
// See https://github.com/rust-lang/rust/issues/23707#issuecomment-557312736
#[derive(Debug, Clone)]
pub(crate) enum InnerArray<'a> {
    Owned(Vec<LhsValue<'a>>),
    Borrowed(&'a (dyn ArraySlice + 'a)),
}

impl<'a> InnerArray<'a> {
    #[inline]
    const fn new() -> Self {
        Self::Owned(Vec::new())
    }

    #[inline]
    fn len(&self) -> usize {
        match self {
            InnerArray::Owned(vec) => vec.len(),
            InnerArray::Borrowed(slice) => slice.len(),
        }
    }

    #[inline]
    fn is_empty(&self) -> bool {
        match self {
            InnerArray::Owned(vec) => vec.is_empty(),
            InnerArray::Borrowed(slice) => slice.is_empty(),
        }
    }

    #[inline]
    fn get(&'a self, idx: usize) -> Option<LhsValue<'a>> {
        match self {
            InnerArray::Owned(vec) => vec.get(idx),
            InnerArray::Borrowed(slice) => slice.get(idx),
        }
    }
}

impl Default for InnerArray<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl Hash for InnerArray<'_> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            InnerArray::Owned(vec) => vec.hash(state),
            InnerArray::Borrowed(slice) => slice.hash(state),
        }
    }
}

/// An array of [`Type`].
#[derive(Debug, Clone)]
pub struct Array<'a> {
    val_type: CompoundType,
    pub(crate) data: InnerArray<'a>,
}

impl<'a> Array<'a> {
    /// Creates a new array
    pub fn new(val_type: impl Into<CompoundType>) -> Self {
        Self {
            val_type: val_type.into(),
            data: InnerArray::Owned(Vec::new()),
        }
    }

    /// Get a reference to an element if it exists
    #[inline]
    pub fn get(&'a self, idx: usize) -> Option<LhsValue<'a>> {
        self.data.get(idx)
    }

    pub(crate) fn as_ref<'b: 'a>(&'b self) -> Array<'b> {
        Array {
            val_type: self.val_type,
            data: match self.data {
                InnerArray::Owned(ref vec) => InnerArray::Borrowed(vec as &dyn ArraySlice),
                InnerArray::Borrowed(slice) => InnerArray::Borrowed(slice),
            },
        }
    }

    /// Converts an `Array` with borrowed data to a fully owned `Array`.
    pub fn into_owned(self) -> Array<'static> {
        Array {
            val_type: self.val_type,
            data: match self.data {
                InnerArray::Owned(vec) => {
                    InnerArray::Owned(vec.into_iter().map(LhsValue::into_owned).collect())
                }
                InnerArray::Borrowed(arr) => {
                    InnerArray::Owned(arr.iter().map(LhsValue::into_owned).collect())
                }
            },
        }
    }

    /// Returns the type of the contained values.
    #[inline]
    pub fn value_type(&self) -> Type {
        self.val_type.into()
    }

    /// Returns the number of elements in the array
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the array contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Extracts a value at index `idx` if it exists.
    pub fn extract(self, idx: usize) -> Option<LhsValue<'a>> {
        let Self { data, .. } = self;
        match data {
            InnerArray::Owned(mut vec) => {
                if idx >= vec.len() {
                    None
                } else {
                    Some(vec.swap_remove(idx))
                }
            }
            InnerArray::Borrowed(arr) => arr.get(idx),
        }
    }

    pub(crate) fn filter_map_to<F>(self, value_type: impl Into<CompoundType>, func: F) -> Self
    where
        F: Fn(LhsValue<'a>) -> Option<LhsValue<'a>>,
    {
        let Self { data, .. } = self;
        let mut vec = match data {
            InnerArray::Owned(vec) => vec,
            InnerArray::Borrowed(arr) => {
                let mut vec = Vec::with_capacity(arr.len());
                vec.extend(arr.iter());
                vec
            }
        };
        let val_type = value_type.into();
        let mut write = 0;
        for read in 0..vec.len() {
            let elem = &mut vec[read];
            if let Some(elem) = func(std::mem::replace(elem, LhsValue::Bool(false))) {
                assert!(elem.get_type() == val_type.into());
                vec[write] = elem;
                write += 1;
            }
        }
        vec.truncate(write);
        Array {
            val_type,
            data: InnerArray::Owned(vec),
        }
    }

    /// Creates a new array from the specified iterator.
    pub fn try_from_iter<V: Into<LhsValue<'a>>>(
        val_type: impl Into<CompoundType>,
        iter: impl IntoIterator<Item = V>,
    ) -> Result<Self, TypeMismatchError> {
        let val_type = val_type.into();
        iter.into_iter()
            .map(|elem| {
                let elem = elem.into();
                let elem_type = elem.get_type();
                if val_type != elem_type.into() {
                    Err(TypeMismatchError {
                        expected: Type::from(val_type).into(),
                        actual: elem_type,
                    })
                } else {
                    Ok(elem)
                }
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|vec| Array {
                val_type,
                data: InnerArray::Owned(vec),
            })
    }

    /// Creates a new array form the specified vector.
    pub fn try_from_vec(
        val_type: impl Into<CompoundType>,
        vec: Vec<LhsValue<'a>>,
    ) -> Result<Self, TypeMismatchError> {
        let val_type = val_type.into();
        for elem in &vec {
            let elem_type = elem.get_type();
            if val_type != elem_type.into() {
                return Err(TypeMismatchError {
                    expected: Type::from(val_type).into(),
                    actual: elem_type,
                });
            }
        }
        Ok(Array {
            val_type,
            data: InnerArray::Owned(vec),
        })
    }

    /// Converts the array into a vector.
    #[inline]
    pub fn into_vec(self) -> Vec<LhsValue<'a>> {
        match self.data {
            InnerArray::Owned(vec) => vec,
            InnerArray::Borrowed(slice) => slice.iter().collect(),
        }
    }
}

impl<'a> PartialEq for Array<'a> {
    #[inline]
    fn eq(&self, other: &Array<'a>) -> bool {
        if self.val_type != other.val_type {
            return false;
        }

        match (&self.data, &other.data) {
            (InnerArray::Owned(vec1), InnerArray::Owned(vec2)) => vec1 == vec2,
            (InnerArray::Borrowed(arr1), InnerArray::Borrowed(arr2)) => arr1.iter().eq(arr2.iter()),
            (InnerArray::Owned(vec), InnerArray::Borrowed(arr)) => arr.eq_slice(vec),
            (InnerArray::Borrowed(arr), InnerArray::Owned(vec)) => arr.eq_slice(vec),
        }
    }
}

impl<'a, T: std::fmt::Debug + Hash + Send + Sync> From<&'a Vec<T>> for Array<'a>
where
    for<'b> &'b T: IntoValue<'b>,
{
    fn from(data: &'a Vec<T>) -> Self {
        Array {
            val_type: <&T>::TYPE.into(),
            data: InnerArray::Borrowed(data as &dyn ArraySlice),
        }
    }
}

impl<'a, T: std::fmt::Debug + Hash + Send + Sync> From<&'a Box<[T]>> for Array<'a>
where
    for<'b> &'b T: IntoValue<'b>,
{
    fn from(data: &'a Box<[T]>) -> Self {
        Array {
            val_type: <&T>::TYPE.into(),
            data: InnerArray::Borrowed(data as &dyn ArraySlice),
        }
    }
}

impl<'a, T: std::fmt::Debug + Hash + Send + Sync> From<&'a Arc<[T]>> for Array<'a>
where
    for<'b> &'b T: IntoValue<'b>,
{
    fn from(data: &'a Arc<[T]>) -> Self {
        Array {
            val_type: <&T>::TYPE.into(),
            data: InnerArray::Borrowed(data as &dyn ArraySlice),
        }
    }
}

impl Eq for Array<'_> {}

impl GetType for Array<'_> {
    fn get_type(&self) -> Type {
        Type::Array(self.val_type)
    }
}

impl Hash for Array<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_type().hash(state);
        self.data.hash(state);
    }
}

impl<'a, V: IntoValue<'a>> FromIterator<V> for Array<'a> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = V>,
    {
        let vec = iter.into_iter().map(IntoValue::into_value).collect();
        Self {
            val_type: V::TYPE.into(),
            data: InnerArray::Owned(vec),
        }
    }
}

enum ArrayIntoIterImpl<'a> {
    Owned(std::vec::IntoIter<LhsValue<'a>>),
    Borrowed(Iter<'a>),
}

pub struct ArrayIntoIter<'a>(ArrayIntoIterImpl<'a>);

impl<'a> Iterator for ArrayIntoIter<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ArrayIntoIter(ArrayIntoIterImpl::Owned(vec_iter)) => vec_iter.next(),
            ArrayIntoIter(ArrayIntoIterImpl::Borrowed(slice_iter)) => slice_iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for ArrayIntoIter<'_> {
    fn len(&self) -> usize {
        match self {
            ArrayIntoIter(ArrayIntoIterImpl::Owned(vec_iter)) => vec_iter.len(),
            ArrayIntoIter(ArrayIntoIterImpl::Borrowed(arr_iter)) => arr_iter.len(),
        }
    }
}

impl<'a> IntoIterator for Array<'a> {
    type Item = LhsValue<'a>;
    type IntoIter = ArrayIntoIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        match self.data {
            InnerArray::Owned(vec) => ArrayIntoIter(ArrayIntoIterImpl::Owned(vec.into_iter())),
            InnerArray::Borrowed(arr) => ArrayIntoIter(ArrayIntoIterImpl::Borrowed(arr.iter())),
        }
    }
}

enum ArrayIterImpl<'slice> {
    Owned(std::slice::Iter<'slice, LhsValue<'slice>>),
    Borrowed(Iter<'slice>),
}

pub struct ArrayIter<'slice>(ArrayIterImpl<'slice>);

impl<'slice> Iterator for ArrayIter<'slice> {
    type Item = LhsValue<'slice>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ArrayIter(ArrayIterImpl::Owned(iter)) => iter.next().map(LhsValue::as_ref),
            ArrayIter(ArrayIterImpl::Borrowed(iter)) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for ArrayIter<'_> {
    fn len(&self) -> usize {
        match self {
            ArrayIter(ArrayIterImpl::Owned(iter)) => iter.len(),
            ArrayIter(ArrayIterImpl::Borrowed(iter)) => iter.len(),
        }
    }
}

impl<'slice> IntoIterator for &'slice Array<'slice> {
    type Item = LhsValue<'slice>;
    type IntoIter = ArrayIter<'slice>;
    fn into_iter(self) -> Self::IntoIter {
        match &self.data {
            InnerArray::Owned(vec) => ArrayIter(ArrayIterImpl::Owned(vec.as_slice().iter())),
            InnerArray::Borrowed(arr) => ArrayIter(ArrayIterImpl::Borrowed(arr.iter())),
        }
    }
}

impl Serialize for Array<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for element in self {
            seq.serialize_element(&element)?;
        }
        seq.end()
    }
}

impl<'de> DeserializeSeed<'de> for &mut Array<'de> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ArrayVisitor<'de, 'a>(&'a mut Array<'de>);

        impl<'de> Visitor<'de> for ArrayVisitor<'de, '_> {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "an array of lhs value")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<(), A::Error>
            where
                A: SeqAccess<'de>,
            {
                let value_type = self.0.value_type();
                let mut vec = match &mut self.0.data {
                    InnerArray::Owned(vec) => std::mem::take(vec),
                    InnerArray::Borrowed(arr) => {
                        let mut vec = Vec::with_capacity(arr.len());
                        vec.extend(arr.iter());
                        vec
                    }
                };
                while let Some(elem) = seq.next_element_seed(LhsValueSeed(&value_type))? {
                    let elem_type = elem.get_type();
                    if value_type != elem_type {
                        return Err(de::Error::custom(format!(
                            "invalid type: {elem_type:?}, expected {value_type:?}"
                        )));
                    }
                    vec.push(elem);
                }
                self.0.data = InnerArray::Owned(vec);
                Ok(())
            }
        }

        deserializer.deserialize_seq(ArrayVisitor(self))
    }
}

/// Typed wrapper over an `Array` which provides
/// infaillible operations.
#[repr(transparent)]
pub struct TypedArray<'a, V>
where
    V: IntoValue<'a>,
{
    array: InnerArray<'a>,
    _marker: std::marker::PhantomData<[V]>,
}

impl<'a, V: IntoValue<'a>> TypedArray<'a, V> {
    /// Creates a new empty typed array.
    #[inline]
    pub const fn new() -> Self {
        const {
            Self {
                array: InnerArray::Owned(Vec::new()),
                _marker: std::marker::PhantomData,
            }
        }
    }

    #[inline]
    fn as_slice(&self) -> &[LhsValue<'a>] {
        match &self.array {
            InnerArray::Owned(vec) => vec,
            InnerArray::Borrowed(_) => unreachable!(),
        }
    }

    #[inline]
    fn as_vec(&mut self) -> &mut Vec<LhsValue<'a>> {
        match &mut self.array {
            InnerArray::Owned(vec) => vec,
            InnerArray::Borrowed(_) => unreachable!(),
        }
    }

    /// Push an element to the back of the array
    #[inline]
    pub fn push(&mut self, value: V) {
        self.as_vec().push(value.into_value())
    }

    /// Returns the number of elements in the array
    #[inline]
    pub fn len(&self) -> usize {
        self.array.len()
    }

    /// Returns true if the array contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.array.is_empty()
    }

    /// Shortens the array, keeping the first `len` elements and dropping the rest.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        self.as_vec().truncate(len);
    }

    /*
    /// Converts the strongly typed array into a borrowed loosely typed array.
    pub fn as_array(&'a self) -> Array<'a> {
        Array {
            val_type: V::TYPE.into(),
            data: InnerArray::Borrowed(self.as_slice()),
        }
    }
    */
}

impl TypedArray<'static, bool> {
    #[inline]
    pub(crate) fn iter(&self) -> impl ExactSizeIterator<Item = &bool> + '_ {
        self.as_slice().iter().map(|value| match value {
            LhsValue::Bool(b) => b,
            _ => unsafe { unreachable_unchecked() },
        })
    }

    #[inline]
    pub(crate) fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = &mut bool> + '_ {
        self.as_vec().iter_mut().map(|value| match value {
            LhsValue::Bool(b) => b,
            _ => unsafe { unreachable_unchecked() },
        })
    }
}

impl<'a, V: IntoValue<'a>> fmt::Debug for TypedArray<'a, V> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_list().entries(self.as_slice().iter()).finish()
    }
}

impl<'a, V: IntoValue<'a>> PartialEq for TypedArray<'a, V> {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<'a, V: Copy + IntoValue<'a>, S: AsRef<[V]>> PartialEq<S> for TypedArray<'a, V> {
    fn eq(&self, other: &S) -> bool {
        other
            .as_ref()
            .iter()
            .copied()
            .map(IntoValue::into_value)
            .eq(self.as_slice().iter())
    }
}

impl<'a, V: IntoValue<'a>> From<TypedArray<'a, V>> for Array<'a> {
    #[inline]
    fn from(value: TypedArray<'a, V>) -> Self {
        Array {
            val_type: V::TYPE.into(),
            data: value.array,
        }
    }
}

impl<'a, V: IntoValue<'a>> Default for TypedArray<'a, V> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, V: IntoValue<'a>> Extend<V> for TypedArray<'a, V> {
    #[inline]
    fn extend<T: IntoIterator<Item = V>>(&mut self, iter: T) {
        self.as_vec()
            .extend(iter.into_iter().map(IntoValue::into_value))
    }
}

impl<'a, V: IntoValue<'a>> FromIterator<V> for TypedArray<'a, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = V>,
    {
        Self {
            array: InnerArray::Owned(iter.into_iter().map(|elem| elem.into_value()).collect()),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, V: IntoValue<'a>> IntoValue<'a> for TypedArray<'a, V> {
    const TYPE: Type = Type::Array(CompoundType::from_type(V::TYPE));

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Array(self.into())
    }
}

impl<'a, V: IntoValue<'a>> TypedArray<'a, TypedArray<'a, V>> {
    /// Returns a reference to an element or None if the index is out of bounds.
    pub fn get(&self, index: usize) -> Option<&TypedArray<'a, V>> {
        self.as_slice().get(index).map(|val| match val {
            LhsValue::Array(array) => {
                // Safety: this is safe because `TypedArray` is a repr(transparent)
                // newtype over `InnerArray`.
                unsafe { std::mem::transmute::<&InnerArray<'a>, &TypedArray<'a, V>>(&array.data) }
            }
            _ => unreachable!(),
        })
    }

    /// Returns a mutable reference to an element or None if the index is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut TypedArray<'a, V>> {
        self.as_vec().get_mut(index).map(|val| match val {
            LhsValue::Array(array) => {
                // Safety: this is safe because `TypedArray` is a repr(transparent)
                // newtype over `InnerArray`.
                unsafe {
                    std::mem::transmute::<&mut InnerArray<'a>, &mut TypedArray<'a, V>>(
                        &mut array.data,
                    )
                }
            }
            _ => unreachable!(),
        })
    }
}

impl<'a, V: IntoValue<'a>> TypedArray<'a, TypedMap<'a, V>> {
    /// Returns a reference to an element or None if the index is out of bounds.
    pub fn get(&self, index: usize) -> Option<&TypedMap<'a, V>> {
        self.as_slice().get(index).map(|val| match val {
            LhsValue::Map(map) => {
                // Safety: this is safe because `TypedMap` is a repr(transparent)
                // newtype over `InnerMap`.
                unsafe { std::mem::transmute::<&InnerMap<'a>, &TypedMap<'a, V>>(&map.data) }
            }
            _ => unreachable!(),
        })
    }

    /// Returns a mutable reference to an element or None if the index is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut TypedMap<'a, V>> {
        self.as_vec().get_mut(index).map(|val| match val {
            LhsValue::Map(map) => {
                // Safety: this is safe because `TypedMap` is a repr(transparent)
                // newtype over `InnerMap`.
                unsafe {
                    std::mem::transmute::<&mut InnerMap<'a>, &mut TypedMap<'a, V>>(&mut map.data)
                }
            }
            _ => unreachable!(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size_of_array() {
        assert_eq!(std::mem::size_of::<Array<'_>>(), 32);
    }

    #[test]
    fn test_borrowed_eq_owned() {
        let mut arr = TypedArray::new();

        arr.push("borrowed");

        let owned = Array::from(arr);

        let borrowed = owned.as_ref();

        assert!(matches!(owned.data, InnerArray::Owned(_)));

        assert!(matches!(borrowed.data, InnerArray::Borrowed(_)));

        assert_eq!(owned, borrowed);

        assert_eq!(borrowed, borrowed.to_owned());
    }

    #[test]
    fn test_typed_array_get_typed_array() {
        let mut array = TypedArray::from_iter([
            TypedArray::from_iter(["a", "b", "c"]),
            TypedArray::from_iter(["d", "e"]),
        ]);

        assert_eq!(*array.get(0).unwrap(), ["a", "b", "c"],);

        assert_eq!(*array.get(1).unwrap(), ["d", "e"]);

        array.get_mut(1).unwrap().push("f");

        assert_eq!(*array.get(1).unwrap(), ["d", "e", "f"]);
    }

    fn key(s: &str) -> Box<[u8]> {
        s.as_bytes().to_vec().into_boxed_slice()
    }

    #[test]
    fn test_typed_array_get_typed_map() {
        let mut array = TypedArray::from_iter([
            TypedMap::from_iter([(key("a"), 42), (key("b"), 1337), (key("c"), 0)]),
            TypedMap::from_iter([(key("d"), 7), (key("e"), 3)]),
        ]);

        assert_eq!(
            array.get(0).unwrap(),
            &[(b"a" as &[u8], 42), (b"b", 1337), (b"c", 0)]
        );

        assert_eq!(array.get(1).unwrap(), &[(b"d" as &[u8], 7), (b"e", 3)]);

        array.get_mut(1).unwrap().insert(key("f"), 99);

        assert_eq!(
            array.get(1).unwrap(),
            &[(b"d" as &[u8], 7), (b"e", 3), (b"f", 99)]
        );
    }

    #[test]
    fn test_array_interface() {
        let vec = vec![
            String::from("one"),
            String::from("two"),
            String::from("three"),
        ];

        let arr = Array::from(&vec);

        dbg!(&arr);

        assert_eq!(arr.len(), 3);

        assert_eq!(arr.get(0), Some(LhsValue::from("one")));
        assert_eq!(arr.get(1), Some(LhsValue::from("two")));
        assert_eq!(arr.get(2), Some(LhsValue::from("three")));
    }
}
