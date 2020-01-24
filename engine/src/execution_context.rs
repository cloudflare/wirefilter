use crate::{
    scheme::{Field, Scheme, SchemeMismatchError},
    types::{GetType, LhsValue, LhsValueSeed, TypeMismatchError},
};
use failure::Fail;
use serde::de::{self, DeserializeSeed, Deserializer, MapAccess, Visitor};
use serde::ser::{Serialize, SerializeMap, Serializer};
use std::borrow::Cow;
use std::fmt;

/// An error that occurs when setting the field value in the [`ExecutionContext`](struct@ExecutionContext)
#[derive(Debug, PartialEq, Fail)]
pub enum SetFieldValueError {
    /// An error that occurs when trying to assign a value of the wrong type to a field.
    #[fail(display = "{}", _0)]
    TypeMismatchError(#[cause] TypeMismatchError),

    /// An error that occurs when trying to set the value of a field from a different scheme.
    #[fail(display = "{}", _0)]
    SchemeMismatchError(#[cause] SchemeMismatchError),
}

/// An execution context stores an associated [`Scheme`](struct@Scheme) and a
/// set of runtime values to execute [`Filter`](::Filter) against.
///
/// It acts as a map in terms of public API, but provides a constant-time
/// index-based access to values for a filter during execution.
#[derive(Debug, PartialEq)]
pub struct ExecutionContext<'e> {
    scheme: &'e Scheme,
    values: Box<[Option<LhsValue<'e>>]>,
}

impl<'e> ExecutionContext<'e> {
    /// Creates an execution context associated with a given scheme.
    ///
    /// This scheme will be used for resolving any field names and indices.
    pub fn new<'s: 'e>(scheme: &'s Scheme) -> Self {
        ExecutionContext {
            scheme,
            values: vec![None; scheme.get_field_count()].into(),
        }
    }

    /// Returns an associated scheme.
    pub fn scheme(&self) -> &'e Scheme {
        self.scheme
    }

    pub(crate) fn get_field_value_unchecked<'s>(&'e self, field: Field<'s>) -> &'e LhsValue<'e> {
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

    /// Sets a runtime value for a given field name.
    pub fn set_field_value<'v: 'e, V: Into<LhsValue<'v>>>(
        &mut self,
        field: Field<'e>,
        value: V,
    ) -> Result<(), SetFieldValueError> {
        if !std::ptr::eq(self.scheme, field.scheme()) {
            return Err(SetFieldValueError::SchemeMismatchError(SchemeMismatchError));
        }
        let value = value.into();

        let field_type = field.get_type();
        let value_type = value.get_type();

        if field_type == value_type {
            self.values[field.index()] = Some(value);
            Ok(())
        } else {
            Err(SetFieldValueError::TypeMismatchError(TypeMismatchError {
                expected: field_type.into(),
                actual: value_type,
            }))
        }
    }
}

impl<'de, 'a> DeserializeSeed<'de> for &'a mut ExecutionContext<'de> {
    type Value = ();

    fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ExecutionContextVisitor<'de, 'a>(&'a mut ExecutionContext<'de>);

        impl<'de, 'a> Visitor<'de> for ExecutionContextVisitor<'de, 'a> {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                write!(formatter, "a map of lhs value")
            }

            fn visit_map<M>(self, mut access: M) -> Result<(), M::Error>
            where
                M: MapAccess<'de>,
            {
                while let Some(key) = access.next_key::<Cow<'_, str>>()? {
                    let field = self
                        .0
                        .scheme
                        .get_field(&key)
                        .map_err(|_| de::Error::custom(format!("unknown field: {}", key)))?;
                    let value =
                        access.next_value_seed::<LhsValueSeed>(LhsValueSeed(&field.get_type()))?;
                    let field = self
                        .0
                        .scheme()
                        .get_field(&key)
                        .map_err(|_| de::Error::custom(format!("unknown field: {}", key)))?;
                    self.0.set_field_value(field, value).map_err(|e| match e {
                        SetFieldValueError::TypeMismatchError(e) => de::Error::custom(format!(
                            "invalid type: {:?}, expected {:?}",
                            e.actual, e.expected
                        )),
                        SetFieldValueError::SchemeMismatchError(_) => unreachable!(),
                    })?;
                }

                Ok(())
            }
        }

        deserializer.deserialize_map(ExecutionContextVisitor(self))
    }
}

impl<'e> Serialize for ExecutionContext<'e> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.values.len()))?;
        for (idx, val) in self.values.iter().enumerate() {
            if let Some(val) = val {
                let key = self.scheme.get_field_from_index(idx).unwrap().name();
                map.serialize_entry(key, val)?;
            }
        }
        map.end()
    }
}

#[test]
fn test_field_value_type_mismatch() {
    use crate::types::Type;

    let scheme = Scheme! { foo: Int };

    let mut ctx = ExecutionContext::new(&scheme);

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
    let scheme = Scheme! { foo: Bool };

    let mut ctx = ExecutionContext::new(&scheme);

    let scheme2 = Scheme! { foo: Bool };

    assert_eq!(
        ctx.set_field_value(scheme2.get_field("foo").unwrap(), LhsValue::Bool(false)),
        Err(SetFieldValueError::SchemeMismatchError(
            SchemeMismatchError {}
        ))
    );
}

#[test]
fn test_serde() {
    use crate::types::{Array, Map, Type};
    use std::net::IpAddr;
    use std::str::FromStr;

    let mut scheme = Scheme::new();
    scheme.add_field("bool".to_string(), Type::Bool).unwrap();
    scheme.add_field("ip".to_string(), Type::Ip).unwrap();
    scheme.add_field("str".to_string(), Type::Bytes).unwrap();
    scheme.add_field("bytes".to_string(), Type::Bytes).unwrap();
    scheme.add_field("num".to_string(), Type::Int).unwrap();
    scheme
        .add_field("arr".to_string(), Type::Array(Box::new(Type::Bool)))
        .unwrap();
    scheme
        .add_field("map".to_string(), Type::Map(Box::new(Type::Int)))
        .unwrap();

    let mut ctx = ExecutionContext::new(&scheme);

    assert_eq!(
        ctx.set_field_value(scheme.get_field("bool").unwrap(), LhsValue::Bool(false)),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(
            scheme.get_field("ip").unwrap(),
            LhsValue::Ip(IpAddr::from_str("127.0.0.1").unwrap())
        ),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("str").unwrap(), "a string"),
        Ok(()),
    );
    assert_eq!(
        ctx.set_field_value(scheme.get_field("bytes").unwrap(), &b"a\xFF\xFFb"[..]),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("num").unwrap(), 42),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("arr").unwrap(), {
            let mut arr = Array::new(Type::Bool);
            arr.push(false.into()).unwrap();
            arr.push(true.into()).unwrap();
            arr
        }),
        Ok(()),
    );

    assert_eq!(
        ctx.set_field_value(scheme.get_field("map").unwrap(), {
            let mut map = Map::new(Type::Int);
            map.insert(b"leet", 1337.into()).unwrap();
            map.insert(b"tabs", 25.into()).unwrap();
            map
        }),
        Ok(()),
    );

    let json = assert_json!(
        ctx,
        {
            "bool": false,
            "ip": "127.0.0.1",
            "str": "a string",
            "bytes": [97, 255, 255, 98],
            "num": 42,
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
            map.insert(b"leet", 1337.into()).unwrap();
            map.insert(b"tabs", 25.into()).unwrap();
            map.insert(b"a\xFF\xFFb", 17.into()).unwrap();
            map
        }),
        Ok(()),
    );

    let json = assert_json!(
        ctx,
        {
            "bool": false,
            "ip": "127.0.0.1",
            "str": "a string",
            "bytes": [97, 255, 255, 98],
            "num": 42,
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
