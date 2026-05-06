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
}

impl Bytes<'_> {
    /// Clones self into a fully owned byte string.
    #[inline]
    pub fn to_owned(&self) -> Bytes<'static> {
        match self {
            Self::Borrowed(b) => Bytes::Owned(Box::from(*b)),
            Self::Owned(b) => Bytes::Owned(b.clone()),
        }
    }

    /// Converts self into a fully owned byte string.
    #[inline]
    pub fn into_owned(self) -> Box<[u8]> {
        match self {
            Self::Borrowed(b) => Box::from(b),
            Self::Owned(b) => b,
        }
    }

    /// Converts self into an owned byte string if necessary
    /// and returns a mutable reference to the bytes.
    #[inline]
    pub fn to_mut(&mut self) -> &mut [u8] {
        if let Self::Borrowed(b) = self {
            *self = Self::Owned(Box::from(*b));
        }
        match self {
            Self::Owned(b) => b,
            Self::Borrowed(_) => unreachable!(),
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
        }
    }
}

impl AsRef<[u8]> for Bytes<'_> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(b) => b,
        }
    }
}

impl Borrow<[u8]> for Bytes<'_> {
    #[inline]
    fn borrow(&self) -> &[u8] {
        match self {
            Self::Borrowed(b) => b,
            Self::Owned(b) => b,
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
