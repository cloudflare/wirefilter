use crate::{
    lhs_types::AsRefIterator,
    types::{
        CompoundType, GetType, IntoValue, LhsValue, LhsValueMut, LhsValueSeed, Type,
        TypeMismatchError,
    },
};
use serde::{
    de::{self, DeserializeSeed, Deserializer, SeqAccess, Visitor},
    ser::SerializeSeq,
    Serialize, Serializer,
};
use std::{
    fmt,
    hash::{Hash, Hasher},
    hint::unreachable_unchecked,
    ops::Deref,
};

// Ideally, we would want to use Cow<'a, LhsValue<'a>> here
// but it doesnt work for unknown reasons
// See https://github.com/rust-lang/rust/issues/23707#issuecomment-557312736
#[derive(Debug, Clone)]
enum InnerArray<'a> {
    Owned(Vec<LhsValue<'a>>),
    Borrowed(&'a [LhsValue<'a>]),
}

impl<'a> InnerArray<'a> {
    #[inline]
    fn as_vec(&mut self) -> &mut Vec<LhsValue<'a>> {
        match self {
            InnerArray::Owned(vec) => vec,
            InnerArray::Borrowed(slice) => {
                *self = InnerArray::Owned(slice.to_vec());
                match self {
                    InnerArray::Owned(vec) => vec,
                    _ => unsafe { unreachable_unchecked() },
                }
            }
        }
    }

    #[inline]
    fn get_mut(&mut self, idx: usize) -> Option<&mut LhsValue<'a>> {
        self.as_vec().get_mut(idx)
    }

    #[inline]
    fn insert(&mut self, idx: usize, value: LhsValue<'a>) {
        self.as_vec().insert(idx, value)
    }

    #[inline]
    fn push(&mut self, value: LhsValue<'a>) {
        self.as_vec().push(value)
    }

    #[inline]
    fn truncate(&mut self, len: usize) {
        match self {
            InnerArray::Owned(vec) => vec.truncate(len),
            InnerArray::Borrowed(slice) => {
                *slice = &slice[..len];
            }
        }
    }
}

impl<'a> Deref for InnerArray<'a> {
    type Target = [LhsValue<'a>];

    #[inline]
    fn deref(&self) -> &Self::Target {
        match self {
            InnerArray::Owned(vec) => &vec[..],
            InnerArray::Borrowed(slice) => slice,
        }
    }
}

/// An array of [`Type`].
#[derive(Debug, Clone)]
pub struct Array<'a> {
    val_type: CompoundType,
    data: InnerArray<'a>,
}

impl<'a> Array<'a> {
    /// Creates a new array
    pub fn new(val_type: impl Into<CompoundType>) -> Self {
        Self {
            val_type: val_type.into(),
            data: InnerArray::Owned(Vec::new()),
        }
    }

    /// Creates a new array with the specified capacity
    pub fn with_capacity(val_type: impl Into<CompoundType>, capacity: usize) -> Self {
        Self {
            val_type: val_type.into(),
            data: InnerArray::Owned(Vec::with_capacity(capacity)),
        }
    }

    /// Get a reference to an element if it exists
    pub fn get(&self, idx: usize) -> Option<&LhsValue<'a>> {
        self.data.get(idx)
    }

    /// Get a mutable reference to an element if it exists
    pub fn get_mut(&mut self, idx: usize) -> Option<LhsValueMut<'_, 'a>> {
        self.data.get_mut(idx).map(LhsValueMut::from)
    }

    /// Inserts an element at index `idx`
    pub fn insert(
        &mut self,
        idx: usize,
        value: impl Into<LhsValue<'a>>,
    ) -> Result<(), TypeMismatchError> {
        let value = value.into();
        let value_type = value.get_type();
        if value_type != self.val_type.into() {
            return Err(TypeMismatchError {
                expected: Type::from(self.val_type).into(),
                actual: value_type,
            });
        }
        self.data.insert(idx, value);
        Ok(())
    }

    /// Push an element to the back of the array
    pub fn push(&mut self, value: impl Into<LhsValue<'a>>) -> Result<(), TypeMismatchError> {
        let value = value.into();
        let value_type = value.get_type();
        if value_type != self.val_type.into() {
            return Err(TypeMismatchError {
                expected: Type::from(self.val_type).into(),
                actual: value_type,
            });
        }
        self.data.push(value);
        Ok(())
    }

    pub(crate) fn as_ref(&'a self) -> Array<'a> {
        Array {
            val_type: self.val_type,
            data: match self.data {
                InnerArray::Owned(ref vec) => InnerArray::Borrowed(&vec[..]),
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
                InnerArray::Borrowed(slice) => {
                    InnerArray::Owned(slice.iter().cloned().map(LhsValue::into_owned).collect())
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

    pub(crate) fn extract(self, idx: usize) -> Option<LhsValue<'a>> {
        let Self { data, .. } = self;
        if idx >= data.len() {
            None
        } else {
            match data {
                InnerArray::Owned(mut vec) => Some(vec.swap_remove(idx)),
                InnerArray::Borrowed(slice) => Some(unsafe { slice.get_unchecked(idx) }.as_ref()),
            }
        }
    }

    pub(crate) fn as_slice(&self) -> &[LhsValue<'a>] {
        &self.data
    }

    pub(crate) fn filter_map_to<F>(self, value_type: impl Into<CompoundType>, func: F) -> Self
    where
        F: Fn(LhsValue<'a>) -> Option<LhsValue<'a>>,
    {
        let Self { mut data, .. } = self;
        let mut vec = std::mem::take(data.as_vec());
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

    /// Try extending the array with elements provided by the specified iterator.
    pub fn try_extend<V, I>(&mut self, iter: I) -> Result<(), TypeMismatchError>
    where
        V: Into<LhsValue<'a>>,
        I: IntoIterator<Item = V>,
    {
        let value_type = self.value_type();
        let vec = self.data.as_vec();
        for elem in iter {
            let elem = elem.into();
            let elem_type = elem.get_type();
            if value_type != elem_type {
                return Err(TypeMismatchError {
                    expected: value_type.into(),
                    actual: elem_type,
                });
            };
            vec.push(elem);
        }
        Ok(())
    }
}

impl<'a> PartialEq for Array<'a> {
    #[inline]
    fn eq(&self, other: &Array<'a>) -> bool {
        self.val_type == other.val_type && self.data.deref() == other.data.deref()
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
        self.data.deref().hash(state);
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

pub enum ArrayIterator<'a> {
    Owned(std::vec::IntoIter<LhsValue<'a>>),
    Borrowed(AsRefIterator<'a, std::slice::Iter<'a, LhsValue<'a>>>),
}

impl<'a> Iterator for ArrayIterator<'a> {
    type Item = LhsValue<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ArrayIterator::Owned(vec_iter) => vec_iter.next(),
            ArrayIterator::Borrowed(slice_iter) => slice_iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl ExactSizeIterator for ArrayIterator<'_> {
    fn len(&self) -> usize {
        match self {
            ArrayIterator::Owned(vec_iter) => vec_iter.len(),
            ArrayIterator::Borrowed(slice_iter) => slice_iter.len(),
        }
    }
}

impl<'a> IntoIterator for Array<'a> {
    type Item = LhsValue<'a>;
    type IntoIter = ArrayIterator<'a>;
    fn into_iter(self) -> Self::IntoIter {
        match self.data {
            InnerArray::Owned(vec) => ArrayIterator::Owned(vec.into_iter()),
            InnerArray::Borrowed(slice) => ArrayIterator::Borrowed(AsRefIterator(slice.iter())),
        }
    }
}

impl<'a, 'b> IntoIterator for &'b Array<'a> {
    type Item = &'b LhsValue<'a>;
    type IntoIter = std::slice::Iter<'b, LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        self.data.iter()
    }
}

impl Serialize for Array<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for element in self.data.iter() {
            seq.serialize_element(element)?;
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
                let vec = self.0.data.as_vec();
                while let Some(elem) = seq.next_element_seed(LhsValueSeed(&value_type))? {
                    let elem_type = elem.get_type();
                    if value_type != elem_type {
                        return Err(de::Error::custom(format!(
                            "invalid type: {elem_type:?}, expected {value_type:?}"
                        )));
                    }
                    vec.push(elem);
                }
                Ok(())
            }
        }

        deserializer.deserialize_seq(ArrayVisitor(self))
    }
}

/// Wrapper type around mutable `Array` to prevent
/// illegal operations like changing the type of
/// its values.
pub struct ArrayMut<'a, 'b>(&'a mut Array<'b>);

impl<'a, 'b> ArrayMut<'a, 'b> {
    /// Push an element to the back of the array
    #[inline]
    pub fn push(&mut self, value: impl Into<LhsValue<'b>>) -> Result<(), TypeMismatchError> {
        self.0.push(value)
    }

    /// Inserts an element at index `idx`
    #[inline]
    pub fn insert(
        &mut self,
        idx: usize,
        value: impl Into<LhsValue<'b>>,
    ) -> Result<(), TypeMismatchError> {
        self.0.insert(idx, value)
    }

    /// Get a mutable reference to an element if it exists
    #[inline]
    pub fn get_mut(&'a mut self, idx: usize) -> Option<LhsValueMut<'a, 'b>> {
        self.0.get_mut(idx).map(LhsValueMut::from)
    }
}

impl<'b> Deref for ArrayMut<'_, 'b> {
    type Target = Array<'b>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, 'b> From<&'a mut Array<'b>> for ArrayMut<'a, 'b> {
    #[inline]
    fn from(arr: &'a mut Array<'b>) -> Self {
        Self(arr)
    }
}

/// Typed wrapper over an `Array` which provides
/// infaillible operations.
#[derive(Debug)]
pub struct TypedArray<'a, V>
where
    V: IntoValue<'a>,
{
    array: Array<'a>,
    _marker: std::marker::PhantomData<[V]>,
}

impl<'a, V: IntoValue<'a>> TypedArray<'a, V> {
    /// Push an element to the back of the array
    #[inline]
    pub fn push(&mut self, value: V) {
        self.array.data.push(value.into_value())
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
        self.array.data.truncate(len);
    }
}

impl TypedArray<'static, bool> {
    #[inline]
    pub(crate) fn iter(&self) -> impl ExactSizeIterator<Item = &bool> + '_ {
        self.array.data.iter().map(|value| match value {
            LhsValue::Bool(b) => b,
            _ => unsafe { unreachable_unchecked() },
        })
    }

    #[inline]
    pub(crate) fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = &mut bool> + '_ {
        self.array
            .data
            .as_vec()
            .iter_mut()
            .map(|value| match value {
                LhsValue::Bool(b) => b,
                _ => unsafe { unreachable_unchecked() },
            })
    }
}

impl<T: AsRef<[bool]>> PartialEq<T> for TypedArray<'static, bool> {
    fn eq(&self, other: &T) -> bool {
        self.iter().eq(other.as_ref())
    }
}

impl<'a, V: IntoValue<'a>> From<TypedArray<'a, V>> for Array<'a> {
    #[inline]
    fn from(value: TypedArray<'a, V>) -> Self {
        value.array
    }
}

impl<'a, V: IntoValue<'a>> Default for TypedArray<'a, V> {
    #[inline]
    fn default() -> Self {
        Self {
            array: Array::new(V::TYPE),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, V: IntoValue<'a>> Extend<V> for TypedArray<'a, V> {
    #[inline]
    fn extend<T: IntoIterator<Item = V>>(&mut self, iter: T) {
        self.array
            .data
            .as_vec()
            .extend(iter.into_iter().map(IntoValue::into_value))
    }
}

impl<'a, V: IntoValue<'a>> FromIterator<V> for TypedArray<'a, V> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = V>,
    {
        Self {
            array: Array::from_iter(iter),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, V: IntoValue<'a>> IntoValue<'a> for TypedArray<'a, V> {
    const TYPE: Type = Type::Array(CompoundType::from_type(V::TYPE));

    #[inline]
    fn into_value(self) -> LhsValue<'a> {
        LhsValue::Array(self.array)
    }
}

#[test]
fn test_size_of_array() {
    assert_eq!(std::mem::size_of::<Array<'_>>(), 32);
}

#[test]
fn test_borrowed_eq_owned() {
    let mut owned = Array::new(Type::Bytes);

    owned
        .push(LhsValue::Bytes("borrowed".as_bytes().into()))
        .unwrap();

    let borrowed = owned.as_ref();

    assert!(matches!(owned.data, InnerArray::Owned(_)));

    assert!(matches!(borrowed.data, InnerArray::Borrowed(_)));

    assert_eq!(owned, borrowed);

    assert_eq!(borrowed, borrowed.to_owned());
}
