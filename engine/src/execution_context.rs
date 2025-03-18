use crate::{
    scheme::{Field, List, Scheme, SchemeMismatchError},
    types::{GetType, LhsValue, LhsValueSeed, Type, TypeMismatchError},
    ListMatcher,
};
use serde::de::{self, DeserializeSeed, Deserializer, MapAccess, Visitor};
use serde::ser::{SerializeMap, SerializeSeq, Serializer};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::fmt;
use std::fmt::Debug;
use thiserror::Error;

/// An error that occurs when setting the field value in the [`crate::ExecutionContext`].
#[derive(Debug, PartialEq, Eq, Error)]
pub enum SetFieldValueError {
    /// An error that occurs when trying to assign a value of the wrong type to a field.
    #[error("{0}")]
    TypeMismatchError(#[source] TypeMismatchError),

    /// An error that occurs when trying to set the value of a field from a different scheme.
    #[error("{0}")]
    SchemeMismatchError(#[source] SchemeMismatchError),
}

/// An error that occurs when previously defined list gets redefined.
#[derive(Debug, PartialEq, Eq, Error)]
#[error("Invalid list matcher {matcher} for list {list}")]
pub struct InvalidListMatcherError {
    matcher: String,
    list: String,
}

/// An execution context stores an associated [`struct@crate::Scheme`] and a
/// set of runtime values to execute [`crate::Filter`] against.
///
/// It acts as a map in terms of public API, but provides a constant-time
/// index-based access to values for a filter during execution.
#[derive(Debug, PartialEq)]
pub struct ExecutionContext<'e, U = ()> {
    scheme: &'e Scheme,
    values: Box<[Option<LhsValue<'e>>]>,
    list_matchers: Box<[Box<dyn ListMatcher>]>,
    user_data: U,
}

impl<'e, U> ExecutionContext<'e, U> {
    /// Creates an execution context associated with a given scheme.
    ///
    /// This scheme will be used for resolving any field names and indices.
    pub fn new<'s: 'e>(scheme: &'s Scheme) -> Self
    where
        U: Default,
    {
        Self::new_with(scheme, Default::default)
    }

    /// Creates an execution context associated with a given scheme.
    ///
    /// This scheme will be used for resolving any field names and indices.
    pub fn new_with<'s: 'e>(scheme: &'s Scheme, f: impl FnOnce() -> U) -> Self {
        ExecutionContext {
            scheme,
            values: vec![None; scheme.field_count()].into(),
            list_matchers: scheme
                .lists()
                .map(|list| list.definition().new_matcher())
                .collect(),
            user_data: f(),
        }
    }

    /// Returns the associated scheme.
    pub fn scheme(&self) -> &'e Scheme {
        self.scheme
    }

    /// Sets a runtime value for a given field name.
    pub fn set_field_value<'v: 'e, V: Into<LhsValue<'v>>>(
        &mut self,
        field: Field<'e>,
        value: V,
    ) -> Result<Option<LhsValue<'e>>, SetFieldValueError> {
        if !std::ptr::eq(self.scheme, field.scheme()) {
            return Err(SetFieldValueError::SchemeMismatchError(SchemeMismatchError));
        }
        let value = value.into();

        let field_type = field.get_type();
        let value_type = value.get_type();

        if field_type == value_type {
            Ok(self.values[field.index()].replace(value))
        } else {
            Err(SetFieldValueError::TypeMismatchError(TypeMismatchError {
                expected: field_type.into(),
                actual: value_type,
            }))
        }
    }

    #[inline]
    pub(crate) fn get_field_value_unchecked(&self, field: Field<'_>) -> &LhsValue<'_> {
        // This is safe because this code is reachable only from Filter::execute
        // which already performs the scheme compatibility check, but check that
        // invariant holds in the future at least in the debug mode.
        debug_assert!(self.scheme() == field.scheme());

        // For now we panic in this, but later we are going to align behaviour
        // with wireshark: resolve all subexpressions that don't have RHS value
        // to `false`.
        self.values[field.index()].as_ref().unwrap_or_else(|| {
            panic!(
                "Field {} was registered but not given a value",
                field.name()
            );
        })
    }

    /// Get the value of a field.
    pub fn get_field_value(&self, field: Field<'_>) -> Option<&LhsValue<'_>> {
        assert!(self.scheme() == field.scheme());

        self.values[field.index()].as_ref()
    }

    #[inline]
    pub(crate) fn get_list_matcher_unchecked(&self, list: List<'_>) -> &dyn ListMatcher {
        debug_assert!(self.scheme() == list.scheme());

        &*self.list_matchers[list.index()]
    }

    /// Get the list matcher object for the specified list type.
    pub fn get_list_matcher(&self, list: List<'_>) -> &dyn ListMatcher {
        assert!(self.scheme() == list.scheme());

        &*self.list_matchers[list.index()]
    }

    /// Get the list matcher object for the specified list type.
    pub fn get_list_matcher_mut(&mut self, list: List<'_>) -> &mut dyn ListMatcher {
        assert!(self.scheme() == list.scheme());

        &mut *self.list_matchers[list.index()]
    }

    /// Get immutable reference to user data stored in
    /// this execution context with [`ExecutionContext::new_with`].
    #[inline]
    pub fn get_user_data(&self) -> &U {
        &self.user_data
    }

    /// Get mutable reference to user data stored in
    /// this execution context with [`ExecutionContext::new_with`].
    #[inline]
    pub fn get_user_data_mut(&mut self) -> &mut U {
        &mut self.user_data
    }

    /// Extract all values and list data into a new [`ExecutionContext`].
    #[inline]
    pub fn take_with<T>(self, default: impl Fn(U) -> T) -> ExecutionContext<'e, T> {
        ExecutionContext {
            scheme: self.scheme,
            values: self.values,
            list_matchers: self.list_matchers,
            user_data: default(self.user_data),
        }
    }

    /// Temporarily borrow all values and list data into a new [`ExecutionContext`].
    #[inline]
    pub fn borrow_with<T>(&mut self, user_data: T) -> ExecutionContextGuard<'_, 'e, U, T> {
        ExecutionContextGuard::new(self, user_data)
    }

    /// Clears the execution context, removing all values and lists
    /// while retaining the allocated memory.
    #[inline]
    pub fn clear(&mut self) {
        self.values.iter_mut().for_each(|value| *value = None);
        self.list_matchers
            .iter_mut()
            .for_each(|list_matcher| list_matcher.clear());
    }
}

/// Guard over a temporarily borrowed [`ExecutionContext`].
/// When the guard is dropped, the original [`ExecutionContext`]
/// is restored.
pub struct ExecutionContextGuard<'a, 'e, U, T> {
    old: &'a mut ExecutionContext<'e, U>,
    new: ExecutionContext<'e, T>,
}

impl<'a, 'e, U, T> ExecutionContextGuard<'a, 'e, U, T> {
    fn new(old: &'a mut ExecutionContext<'e, U>, user_data: T) -> Self {
        let scheme = old.scheme();
        let values = std::mem::take(&mut old.values);
        let list_matchers = std::mem::take(&mut old.list_matchers);

        let new = ExecutionContext {
            scheme,
            values,
            list_matchers,
            user_data,
        };

        Self { old, new }
    }
}

impl<'e, U, T> std::ops::Deref for ExecutionContextGuard<'_, 'e, U, T> {
    type Target = ExecutionContext<'e, T>;

    fn deref(&self) -> &Self::Target {
        &self.new
    }
}

impl<U, T> std::ops::DerefMut for ExecutionContextGuard<'_, '_, U, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.new
    }
}

impl<U, T> Drop for ExecutionContextGuard<'_, '_, U, T> {
    fn drop(&mut self) {
        self.old.values = std::mem::take(&mut self.new.values);
        self.old.list_matchers = std::mem::take(&mut self.new.list_matchers);
    }
}

#[derive(Serialize, Deserialize)]
struct ListData {
    #[serde(rename = "type")]
    ty: Type,
    data: serde_json::Value,
}

impl<'de, U> DeserializeSeed<'de> for &mut ExecutionContext<'de, U> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ExecutionContextVisitor<'de, 'a, U>(&'a mut ExecutionContext<'de, U>);

        impl<'de, U> Visitor<'de> for ExecutionContextVisitor<'de, '_, U> {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a map of lhs value")
            }

            fn visit_map<M>(self, mut access: M) -> Result<(), M::Error>
            where
                M: MapAccess<'de>,
            {
                while let Some(key) = access.next_key::<Cow<'_, str>>()? {
                    if key == "$lists" {
                        // Deserialize lists
                        let vec = access.next_value::<Vec<ListData>>()?;
                        for ListData { ty, data } in vec.into_iter() {
                            let list = self.0.scheme.get_list(&ty).ok_or_else(|| {
                                de::Error::custom(format!("unknown list for type: {ty:?}"))
                            })?;
                            self.0.list_matchers[list.index()] = list
                                .definition()
                                .matcher_from_json_value(ty, data)
                                .map_err(|err| {
                                    de::Error::custom(format!(
                                        "failed to deserialize list matcher: {err:?}"
                                    ))
                                })?;
                        }
                    } else {
                        let field = self
                            .0
                            .scheme
                            .get_field(&key)
                            .map_err(|_| de::Error::custom(format!("unknown field: {key}")))?;
                        let value = access
                            .next_value_seed::<LhsValueSeed<'_>>(LhsValueSeed(&field.get_type()))?;
                        let field = self
                            .0
                            .scheme()
                            .get_field(&key)
                            .map_err(|_| de::Error::custom(format!("unknown field: {key}")))?;
                        self.0.set_field_value(field, value).map_err(|e| match e {
                            SetFieldValueError::TypeMismatchError(e) => de::Error::custom(format!(
                                "invalid type: {:?}, expected {:?}",
                                e.actual, e.expected
                            )),
                            SetFieldValueError::SchemeMismatchError(_) => unreachable!(),
                        })?;
                    }
                }

                Ok(())
            }
        }

        deserializer.deserialize_map(ExecutionContextVisitor(self))
    }
}

impl Serialize for ExecutionContext<'_> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.values.len()))?;
        for field in self.scheme().fields() {
            if let Some(Some(value)) = self.values.get(field.index()) {
                map.serialize_entry(field.name(), value)?;
            }
        }

        struct ListMatcherSlice<'a>(&'a Scheme, &'a [Box<dyn ListMatcher>]);

        impl Serialize for ListMatcherSlice<'_> {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let mut seq = serializer.serialize_seq(Some(self.1.len()))?;
                for list in self.0.lists() {
                    let data = self.1[list.index()].to_json_value();
                    if data != serde_json::Value::Null {
                        seq.serialize_element(&ListData {
                            ty: list.get_type(),
                            data,
                        })?;
                    }
                }
                seq.end()
            }
        }

        if !self.list_matchers.is_empty() {
            map.serialize_entry(
                "$lists",
                &ListMatcherSlice(self.scheme, &self.list_matchers),
            )?;
        }
        map.end()
    }
}

#[test]
fn test_field_value_type_mismatch() {
    use crate::types::Type;

    let scheme = Scheme! { foo: Int }.build();

    let mut ctx = ExecutionContext::<()>::new(&scheme);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("foo").unwrap(), LhsValue::Bool(false)),
        Err(SetFieldValueError::TypeMismatchError(TypeMismatchError {
            expected: Type::Int.into(),
            actual: Type::Bool,
        }))
    );
}

#[test]
fn test_scheme_mismatch() {
    let scheme = Scheme! { foo: Bool }.build();

    let mut ctx = ExecutionContext::<()>::new(&scheme);

    let scheme2 = Scheme! { foo: Bool }.build();

    assert_eq!(
        ctx.set_field_value(scheme2.get_field("foo").unwrap(), LhsValue::Bool(false)),
        Err(SetFieldValueError::SchemeMismatchError(
            SchemeMismatchError {}
        ))
    );
}

#[test]
fn test_serde() {
    use crate::lhs_types::{Array, Map};
    use crate::types::Type;
    use std::net::IpAddr;
    use std::str::FromStr;

    let scheme = Scheme! {
        bool: Bool,
        ip: Ip,
        str: Bytes,
        bytes: Bytes,
        num: Int,
        min_num: Int,
        max_num: Int,
        arr: Array(Bool),
        map: Map(Int),
    }
    .build();

    let mut ctx = ExecutionContext::new(&scheme);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("bool").unwrap(), LhsValue::Bool(false)),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(
            scheme.get_field("ip").unwrap(),
            LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap())
        ),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("str").unwrap(), "a string"),
        Ok(None),
    );
    assert_eq!(
        ctx.set_field_value(scheme.get_field("bytes").unwrap(), &b"a\xFF\xFFb"[..]),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("num").unwrap(), 42),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("min_num").unwrap(), i64::MIN),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("max_num").unwrap(), i64::MAX),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("arr").unwrap(), {
            Array::from_iter([false, true])
        }),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("map").unwrap(), {
            let mut map = Map::new(Type::Int);
            map.insert(b"leet", 1337).unwrap();
            map.insert(b"tabs", 25).unwrap();
            map
        }),
        Ok(None),
    );

    let json = assert_json!(
        ctx,
        {
            "bool": false,
            "ip": "127.0.0.1",
            "str": "a string",
            "bytes": [97, 255, 255, 98],
            "num": 42,
            "min_num": i64::MIN,
            "max_num": i64::MAX,
            "arr": [false, true],
            "map": {
                "leet": 1337,
                "tabs": 25,
            }
        }
    )
    .to_string();

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_str(&json);
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_slice(json.as_bytes());
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx3 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_reader(json.as_bytes());
    ctx3.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx3);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("map").unwrap(), {
            let mut map = Map::new(Type::Int);
            map.insert(b"leet", 1337).unwrap();
            map.insert(b"tabs", 25).unwrap();
            map.insert(b"a\xFF\xFFb", 17).unwrap();
            map
        }),
        Ok(Some({
            let mut map = Map::new(Type::Int);
            map.insert(b"leet", 1337).unwrap();
            map.insert(b"tabs", 25).unwrap();
            map.into()
        })),
    );

    let json = assert_json!(
        ctx,
        {
            "bool": false,
            "ip": "127.0.0.1",
            "str": "a string",
            "bytes": [97, 255, 255, 98],
            "num": 42,
            "min_num": i64::MIN,
            "max_num": i64::MAX,
            "arr": [false, true],
            "map": [
                [[97, 255, 255, 98], 17],
                ["leet", 1337],
                ["tabs", 25]
            ]
        }
    )
    .to_string();

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_str(&json);
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx2 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_slice(json.as_bytes());
    ctx2.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx2);

    let mut ctx3 = ExecutionContext::new(&scheme);
    let mut deserializer = serde_json::Deserializer::from_reader(json.as_bytes());
    ctx3.deserialize(&mut deserializer).unwrap();
    assert_eq!(ctx, ctx3);
}

#[test]
fn test_clear() {
    use std::net::IpAddr;
    use std::str::FromStr;

    let scheme = Scheme! {
        bool: Bool,
        ip: Ip,
    }
    .build();

    let bool_field = scheme.get_field("bool").unwrap();
    let ip_field = scheme.get_field("ip").unwrap();

    let mut ctx = ExecutionContext::<'_, ()>::new(&scheme);

    assert_eq!(
        ctx.set_field_value(bool_field, LhsValue::Bool(false)),
        Ok(None),
    );

    assert_eq!(
        ctx.set_field_value(
            ip_field,
            LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap())
        ),
        Ok(None),
    );

    assert_eq!(
        ctx.get_field_value(bool_field),
        Some(&LhsValue::Bool(false))
    );
    assert_eq!(
        ctx.get_field_value(ip_field),
        Some(&LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap()))
    );

    ctx.clear();

    assert_eq!(ctx.get_field_value(bool_field), None);
    assert_eq!(ctx.get_field_value(ip_field), None);
}
