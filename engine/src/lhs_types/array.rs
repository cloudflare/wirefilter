use crate::{
    lhs_types::AsRefIterator,
    types::{GetType, LhsValue, LhsValueSeed, Type, TypeMismatchError},
};
use serde::{
    de::{self, DeserializeSeed, Deserializer, SeqAccess, Visitor},
    ser::SerializeSeq,
    Serialize, Serializer,
};
use std::{borrow::Cow, fmt, ops::Deref};

// Ideally, we would want to use Cow<'a, LhsValue<'a>> here
// but it doesnt work for unknown reasons
// See https://github.com/rust-lang/rust/issues/23707#issuecomment-557312736
#[derive(Debug, Clone, PartialEq, Eq)]
enum InnerArray<'a> {
    Owned(Vec<LhsValue<'a>>),
    Borrowed(&'a [LhsValue<'a>]),
}

impl<'a> InnerArray<'a> {
    fn get_mut(&mut self, idx: usize) -> Option<&mut LhsValue<'a>> {
        if let InnerArray::Borrowed(slice) = self {
            *self = InnerArray::Owned(slice.to_vec());
        }
        match self {
            InnerArray::Owned(vec) => vec.get_mut(idx),
            InnerArray::Borrowed(_) => unreachable!(),
        }
    }

    fn insert(&mut self, idx: usize, value: LhsValue<'a>) {
        if let InnerArray::Borrowed(slice) = self {
            *self = InnerArray::Owned(slice.to_vec());
        }
        match self {
            InnerArray::Owned(vec) => vec.insert(idx, value),
            InnerArray::Borrowed(_) => unreachable!(),
        }
    }

    fn push(&mut self, value: LhsValue<'a>) {
        if let InnerArray::Borrowed(slice) = self {
            *self = InnerArray::Owned(slice.to_vec());
        }
        match self {
            InnerArray::Owned(vec) => vec.push(value),
            InnerArray::Borrowed(_) => unreachable!(),
        }
    }
}

impl<'a> Deref for InnerArray<'a> {
    type Target = [LhsValue<'a>];

    fn deref(&self) -> &Self::Target {
        match self {
            InnerArray::Owned(vec) => &vec[..],
            InnerArray::Borrowed(slice) => slice,
        }
    }
}

/// An array of [`Type`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Array<'a> {
    val_type: Cow<'a, Type>,
    data: InnerArray<'a>,
}

impl<'a> Array<'a> {
    /// Creates a new array
    pub fn new(val_type: Type) -> Self {
        Self {
            val_type: Cow::Owned(val_type),
            data: InnerArray::Owned(Vec::new()),
        }
    }

    /// Get a reference to an element if it exists
    pub fn get(&self, idx: usize) -> Option<&LhsValue<'a>> {
        self.data.get(idx)
    }

    /// Get a mutable reference to an element if it exists
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut LhsValue<'a>> {
        self.data.get_mut(idx)
    }

    /// Inserts an element at index `idx`
    pub fn insert(&mut self, idx: usize, value: LhsValue<'a>) -> Result<(), TypeMismatchError> {
        let value_type = value.get_type();
        if *self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone().into_owned().into(),
                actual: value_type,
            });
        }
        self.data.insert(idx, value);
        Ok(())
    }

    /// Push an element to the back of the array
    pub fn push(&mut self, value: LhsValue<'a>) -> Result<(), TypeMismatchError> {
        let value_type = value.get_type();
        if *self.val_type != value_type {
            return Err(TypeMismatchError {
                expected: self.val_type.clone().into_owned().into(),
                actual: value_type,
            });
        }
        self.data.push(value);
        Ok(())
    }

    pub(crate) fn as_ref(&'a self) -> Array<'a> {
        Array {
            val_type: match self.val_type {
                Cow::Owned(ref ty) => Cow::Borrowed(ty),
                Cow::Borrowed(ty) => Cow::Borrowed(ty),
            },
            data: match self.data {
                InnerArray::Owned(ref vec) => InnerArray::Borrowed(&vec[..]),
                InnerArray::Borrowed(ref slice) => InnerArray::Borrowed(slice),
            },
        }
    }

    /// Returns the type of the contained values.
    pub fn value_type(&self) -> &Type {
        &self.val_type
    }

    /// Returns the number of elements in the array
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns true if the array contains no elements.
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
}

impl<'a> GetType for Array<'a> {
    fn get_type(&self) -> Type {
        Type::Array(Box::new(self.val_type.clone().into_owned()))
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

impl<'a> IntoIterator for &'a Array<'a> {
    type Item = &'a LhsValue<'a>;
    type IntoIter = std::slice::Iter<'a, LhsValue<'a>>;
    fn into_iter(self) -> Self::IntoIter {
        (&self.data).iter()
    }
}

impl<'a> Extend<LhsValue<'a>> for Array<'a> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = LhsValue<'a>>,
    {
        if let InnerArray::Borrowed(slice) = self.data {
            self.data = InnerArray::Owned(slice.to_vec());
        }
        let value_type = self.value_type().clone();
        match self.data {
            InnerArray::Owned(ref mut vec) => vec.extend(
                iter.into_iter()
                    .inspect(|elem| assert!(elem.get_type() == value_type)),
            ),
            InnerArray::Borrowed(_) => unreachable!(),
        }
    }
}

impl<'a> Serialize for Array<'a> {
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

impl<'de, 'a> DeserializeSeed<'de> for &'a mut Array<'de> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ArrayVisitor<'de, 'a>(&'a mut Array<'de>);

        impl<'de, 'a> Visitor<'de> for ArrayVisitor<'de, 'a> {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "an array of lhs value")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<(), A::Error>
            where
                A: SeqAccess<'de>,
            {
                while let Some(elem) = seq.next_element_seed(LhsValueSeed(self.0.value_type()))? {
                    self.0.push(elem).map_err(|e| {
                        de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            e.actual, e.expected
                        ))
                    })?;
                }
                Ok(())
            }
        }

        deserializer.deserialize_seq(ArrayVisitor(self))
    }
}
