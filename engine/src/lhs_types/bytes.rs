#[cfg(feature = "get-size2")]
use get_size2::{GetSize, GetSizeTracker};
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::borrow::{Borrow, Cow};
use std::hash::{Hash, Hasher};
use std::ops::Deref;

/// A byte string.
#[derive(Debug, Clone)]
pub enum Bytes<'a> {
    /// Borrowed byte string.
    Borrowed(&'a [u8]),
    /// Owned byte string.
    Owned(Box<[u8]>),
    /// Byte string backed by an existing shared buffer.
    /// Newly allocated byte strings use [`Self::Owned`].
    #[cfg(feature = "bytes")]
    Shared(bytes::Bytes),
}

#[cfg(feature = "get-size2")]
impl GetSize for Bytes<'_> {
    fn get_heap_size_with_tracker<T: GetSizeTracker>(&self, tracker: T) -> (usize, T) {
        match self {
            Self::Owned(bytes) => bytes.get_heap_size_with_tracker(tracker),
            #[cfg(feature = "bytes")]
            Self::Shared(bytes) => bytes.get_heap_size_with_tracker(tracker),
            Self::Borrowed(_) => (0, tracker),
        }
    }
}

impl<'a> Bytes<'a> {
    /// Clones self into a fully owned byte string.
    #[inline]
    pub fn to_owned(&self) -> Bytes<'static> {
        match self {
            Self::Borrowed(b) => Bytes::Owned(Box::from(*b)),
            Self::Owned(b) => Bytes::Owned(b.clone()),
            #[cfg(feature = "bytes")]
            Self::Shared(b) => Bytes::Shared(b.clone()),
        }
    }

    /// Converts borrowed data to owned storage, retaining owned and shared buffers.
    #[inline]
    pub fn into_owned(self) -> Bytes<'static> {
        match self {
            Self::Borrowed(b) => Bytes::Owned(Box::from(b)),
            Self::Owned(b) => Bytes::Owned(b),
            #[cfg(feature = "bytes")]
            Self::Shared(b) => Bytes::Shared(b),
        }
    }

    /// Converts self into an owned byte string if necessary
    /// and returns a mutable reference to the bytes.
    #[inline]
    pub fn to_mut(&mut self) -> &mut [u8] {
        if !matches!(self, Self::Owned(_)) {
            *self = Self::Owned(Box::from(self.as_ref()));
        }
        match self {
            Self::Owned(b) => b,
            Self::Borrowed(_) => unreachable!(),
            #[cfg(feature = "bytes")]
            Self::Shared(_) => unreachable!(),
        }
    }

    /// Converts this byte string into a mutable vector, reusing its allocation
    /// when possible. Shared data is copied if its allocation cannot be reused.
    #[inline]
    pub fn into_vec(self) -> Vec<u8> {
        match self {
            Self::Borrowed(b) => b.to_vec(),
            Self::Owned(b) => b.into_vec(),
            #[cfg(feature = "bytes")]
            Self::Shared(b) => b.into(),
        }
    }

    /// Shortens the byte string, keeping only the first `len` elements.
    #[inline]
    pub fn truncate(&mut self, len: usize) {
        match self {
            Self::Borrowed(slice) => {
                *slice = &slice[..len];
            }
            Self::Owned(data) => {
                let mut vec = Vec::from(std::mem::take(data));
                vec.truncate(len);
                *data = Box::from(vec);
            }
            #[cfg(feature = "bytes")]
            Self::Shared(data) => data.truncate(len),
        }
    }
}

impl Deref for Bytes<'_> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(b) => b,
            #[cfg(feature = "bytes")]
            Self::Shared(b) => b,
        }
    }
}

impl AsRef<[u8]> for Bytes<'_> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(b) => b,
            #[cfg(feature = "bytes")]
            Self::Shared(b) => b,
        }
    }
}

impl Borrow<[u8]> for Bytes<'_> {
    #[inline]
    fn borrow(&self) -> &[u8] {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(b) => b,
            #[cfg(feature = "bytes")]
            Self::Shared(b) => b,
        }
    }
}

impl<'a> From<&'a [u8]> for Bytes<'a> {
    #[inline]
    fn from(value: &'a [u8]) -> Self {
        Bytes::Borrowed(value)
    }
}

impl<'a, const N: usize> From<&'a [u8; N]> for Bytes<'a> {
    #[inline]
    fn from(value: &'a [u8; N]) -> Self {
        Bytes::Borrowed(value)
    }
}

impl From<Box<[u8]>> for Bytes<'static> {
    #[inline]
    fn from(value: Box<[u8]>) -> Self {
        Bytes::Owned(value)
    }
}

impl From<Vec<u8>> for Bytes<'static> {
    #[inline]
    fn from(value: Vec<u8>) -> Self {
        Bytes::Owned(value.into_boxed_slice())
    }
}

#[cfg(feature = "bytes")]
impl From<bytes::Bytes> for Bytes<'static> {
    #[inline]
    fn from(value: bytes::Bytes) -> Self {
        Bytes::Shared(value)
    }
}

impl<'a> From<Cow<'a, [u8]>> for Bytes<'a> {
    #[inline]
    fn from(value: Cow<'a, [u8]>) -> Self {
        match value {
            Cow::Borrowed(b) => Self::Borrowed(b),
            Cow::Owned(b) => Self::Owned(b.into_boxed_slice()),
        }
    }
}

impl<'a> From<&'a str> for Bytes<'a> {
    #[inline]
    fn from(value: &'a str) -> Self {
        Bytes::Borrowed(value.as_bytes())
    }
}

impl From<Box<str>> for Bytes<'static> {
    #[inline]
    fn from(value: Box<str>) -> Self {
        Bytes::Owned(value.into_boxed_bytes())
    }
}

impl<'a> From<&'a Box<str>> for Bytes<'a> {
    #[inline]
    fn from(value: &'a Box<str>) -> Self {
        Bytes::Borrowed(value.as_bytes())
    }
}

impl From<String> for Bytes<'static> {
    #[inline]
    fn from(value: String) -> Self {
        // Call into_boxed_str in order to reduce memory usage
        Bytes::Owned(value.into_boxed_str().into_boxed_bytes())
    }
}

impl<'a> From<&'a String> for Bytes<'a> {
    #[inline]
    fn from(value: &'a String) -> Self {
        Bytes::Borrowed(value.as_bytes())
    }
}

impl<'a> From<Cow<'a, str>> for Bytes<'a> {
    #[inline]
    fn from(value: Cow<'a, str>) -> Self {
        match value {
            Cow::Borrowed(b) => Self::Borrowed(b.as_bytes()),
            Cow::Owned(b) => Self::Owned(b.into_boxed_str().into_boxed_bytes()),
        }
    }
}

impl PartialEq for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl PartialEq<[u8]> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &[u8]) -> bool {
        &**self == other
    }
}

impl PartialEq<&[u8]> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &&[u8]) -> bool {
        &**self == *other
    }
}

impl<const N: usize> PartialEq<[u8; N]> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &[u8; N]) -> bool {
        **self == *other
    }
}

impl<const N: usize> PartialEq<&[u8; N]> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &&[u8; N]) -> bool {
        &**self == *other
    }
}

impl PartialEq<Vec<u8>> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        &**self == other
    }
}

impl PartialEq<str> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        &**self == other.as_bytes()
    }
}

impl PartialEq<&str> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        &**self == other.as_bytes()
    }
}

impl PartialEq<String> for Bytes<'_> {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        &**self == other.as_bytes()
    }
}

impl Eq for Bytes<'_> {}

impl Hash for Bytes<'_> {
    #[inline]
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.deref().hash(h);
    }
}

impl Serialize for Bytes<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if let Ok(s) = std::str::from_utf8(self) {
            serializer.serialize_str(s)
        } else {
            serializer.serialize_bytes(self)
        }
    }
}

struct BytesVisitor;

impl<'de> Visitor<'de> for BytesVisitor {
    type Value = Bytes<'de>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a byte string")
    }

    fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Bytes::from(v.to_vec()))
    }

    fn visit_byte_buf<E>(self, v: Vec<u8>) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Bytes::from(v))
    }

    fn visit_borrowed_bytes<E>(self, v: &'de [u8]) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Bytes::Borrowed(v))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Bytes::from(v.as_bytes().to_vec()))
    }

    fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Bytes::from(v))
    }

    fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        Ok(Bytes::Borrowed(v.as_bytes()))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: serde::de::SeqAccess<'de>,
    {
        let mut vec = Vec::<u8>::with_capacity(seq.size_hint().unwrap_or_default());
        while let Some(val) = seq.next_element()? {
            vec.push(val);
        }

        Ok(Bytes::from(vec))
    }
}

impl<'de> Deserialize<'de> for Bytes<'de> {
    fn deserialize<D>(deserializer: D) -> Result<Bytes<'de>, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_bytes(BytesVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(feature = "bytes")]
    use crate::{LhsValue, TypedMap};
    #[cfg(feature = "bytes")]
    use std::hash::BuildHasher;

    #[test]
    fn test_into_owned_storage() {
        let mut borrowed = b"borrowed".to_vec();
        let copied: Bytes<'static> = Bytes::Borrowed(&borrowed).into_owned();
        borrowed[0] = b'X';
        assert!(matches!(copied, Bytes::Owned(_)));
        assert_eq!(copied, b"borrowed");

        let owned = Bytes::from(b"owned".to_vec());
        let ptr = owned.as_ptr();
        let moved: Bytes<'static> = owned.into_owned();
        assert!(matches!(moved, Bytes::Owned(_)));
        assert_eq!(moved.as_ptr(), ptr);
        assert_eq!(moved, b"owned");
    }

    #[test]
    fn test_into_vec_storage() {
        let mut borrowed = b"borrowed".to_vec();
        let copied = Bytes::Borrowed(&borrowed).into_vec();
        borrowed[0] = b'X';
        assert_eq!(copied, b"borrowed");

        let owned = Bytes::from(b"owned".to_vec());
        let ptr = owned.as_ptr();
        let moved = owned.into_vec();
        assert_eq!(moved.as_ptr(), ptr);
        assert_eq!(moved, b"owned");
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_clone() {
        let original = bytes::Bytes::from(b"shared".to_vec());
        let bytes = Bytes::from(original.clone());
        let cloned = bytes.clone();
        let owned: Bytes<'static> = bytes.to_owned();
        let moved: Bytes<'static> = bytes.into_owned();

        for value in [cloned, owned, moved] {
            assert!(matches!(value, Bytes::Shared(_)));
            assert_eq!(value.as_ptr(), original.as_ptr());
            assert_eq!(value, b"shared");
        }
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_into_vec() {
        let unique = bytes::Bytes::from(b"unique".to_vec());
        let ptr = unique.as_ptr();
        let moved = Bytes::Shared(unique).into_vec();
        assert_eq!(moved.as_ptr(), ptr);
        assert_eq!(moved, b"unique");

        let shared = bytes::Bytes::from(b"shared".to_vec());
        let mut copied = Bytes::Shared(shared.clone()).into_vec();
        copied[0] = b'X';
        assert_eq!(copied, b"Xhared");
        assert_eq!(shared.as_ref(), b"shared");
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_mutation() {
        let original = bytes::Bytes::from(b"shared".to_vec());
        let mut bytes = Bytes::from(original.clone());
        bytes.to_mut().make_ascii_uppercase();

        assert!(matches!(bytes, Bytes::Owned(_)));
        assert_eq!(bytes, b"SHARED");
        assert_eq!(original.as_ref(), b"shared");
        assert_eq!(bytes.clone().into_owned().as_ref(), b"SHARED");
        assert_eq!(Bytes::from(original).into_owned().as_ref(), b"shared");
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_truncate() {
        let original = bytes::Bytes::from(b"shared".to_vec());
        let mut bytes = Bytes::from(original.clone());
        bytes.truncate(3);
        assert!(matches!(bytes, Bytes::Shared(_)));
        assert_eq!(bytes.as_ptr(), original.as_ptr());
        assert_eq!(bytes, b"sha");
        bytes.truncate(6);
        assert_eq!(bytes, b"sha");
        bytes.truncate(0);
        assert!(bytes.is_empty());
        assert_eq!(original.as_ref(), b"shared");
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_traits() {
        let hasher = std::collections::hash_map::RandomState::new();
        for slice in [b"shared".as_slice(), b"\x00\xff"] {
            let bytes = Bytes::from(bytes::Bytes::copy_from_slice(slice));
            assert_eq!(bytes.deref(), slice);
            assert_eq!(bytes.as_ref(), slice);
            assert_eq!(Borrow::<[u8]>::borrow(&bytes), slice);
            assert_eq!(bytes, Bytes::Borrowed(slice));
            assert_eq!(hasher.hash_one(&bytes), hasher.hash_one(slice));
            let json = serde_json::to_string(&bytes).unwrap();
            assert_eq!(
                json,
                serde_json::to_string(&Bytes::Borrowed(slice)).unwrap()
            );
            assert_eq!(serde_json::from_str::<Bytes<'_>>(&json).unwrap(), bytes);
        }
    }

    #[cfg(feature = "bytes")]
    #[test]
    fn test_shared_bytes_into_owned_value() {
        let original = bytes::Bytes::from(b"shared".to_vec());
        let value: LhsValue<'_> = original.clone().into();
        let LhsValue::Bytes(Bytes::Shared(bytes)) = value.into_owned() else {
            panic!("shared value changed storage");
        };
        assert_eq!(bytes.as_ptr(), original.as_ptr());

        let map = TypedMap::from_iter([(original.clone().into(), original.clone())]);
        let value: LhsValue<'_> = map.into();
        let LhsValue::Map(map) = value.into_owned() else {
            panic!("expected a map");
        };
        let (Bytes::Shared(key), LhsValue::Bytes(Bytes::Shared(value))) =
            map.into_iter().next().unwrap()
        else {
            panic!("shared map entry changed storage");
        };
        assert_eq!(key.as_ptr(), original.as_ptr());
        assert_eq!(value.as_ptr(), original.as_ptr());
    }

    #[cfg(all(feature = "bytes", feature = "get-size2"))]
    #[test]
    fn test_shared_bytes_get_size() {
        let bytes = Bytes::from(bytes::Bytes::from(b"shared".to_vec()));
        assert_eq!(
            bytes.get_size(),
            std::mem::size_of_val(&bytes) + bytes.len()
        );
    }

    #[test]
    fn test_bytes_deserialize() {
        let bytes = serde_json::from_str::<Bytes<'_>>("\"a JSON string with unicode ❤\"").unwrap();
        assert_eq!(
            bytes,
            Bytes::from(&b"a JSON string with unicode \xE2\x9D\xA4"[..])
        );

        let bytes =
            serde_json::from_str::<Bytes<'_>>("\"a JSON string with escaped-unicode \\u2764\"")
                .unwrap();
        assert_eq!(
            bytes,
            Bytes::from(&b"a JSON string with escaped-unicode \xE2\x9D\xA4"[..])
        );

        let bytes =
            serde_json::from_str::<Bytes<'_>>("[97, 32, 74, 83, 79, 78, 32, 115, 116, 114, 105, 110, 103, 32, 102, 114, 111, 109, 32, 105, 110, 116, 101, 103, 101, 114, 32, 97, 114, 114, 97, 121]")
                .unwrap();
        assert_eq!(bytes, Bytes::from(&b"a JSON string from integer array"[..]));
    }
}
