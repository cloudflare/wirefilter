use crate::LhsValue;
use crate::Type;
use serde_json::Value;
use std::any::Any;
use std::fmt::Debug;

/// Defines a new list to match against.
///
/// `ListDefinition` needs to be registered in the `Scheme` for a given `Type`.
/// See `Scheme::add_list`.
pub trait ListDefinition: Debug + Sync + Send {
    /// Converts a deserialized `serde_json::Value` into a `ListMatcher`.
    ///
    /// This method is necessary to support deserialization of lists during the
    /// the deserialization of an `ExecutionContext`.
    fn matcher_from_json_value(
        &self,
        ty: Type,
        value: Value,
    ) -> Result<ListMatcherWrapper, serde_json::Error>;

    /// Verify an object is a valid `ListMatcher`.
    fn is_valid_matcher(&self, matcher: &dyn Any) -> bool;
}

/// Implement this Trait to match a given `LhsValue` against a list.
pub trait ListMatcher {
    /// Returns true if `val` is in the given list.
    fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool;

    /// Convert the list matcher to a serde_json::Value in order to serialize it.
    fn to_json_value(&self) -> Value;
}

/// Wrapper to ensure that any ListMatcher implements the required Traits.
pub struct ListMatcherWrapper {
    inner: Box<dyn Any + Send + Sync>,
    eq_cb: fn(&(dyn Any + Send + Sync), &(dyn Any + Send + Sync)) -> bool,
    fmt_cb: fn(&(dyn Any + Send + Sync), &mut std::fmt::Formatter<'_>) -> std::fmt::Result,
    match_cb: fn(&(dyn Any + Send + Sync), &str, &LhsValue<'_>) -> bool,
    to_json_value_cb: fn(&(dyn Any + Send + Sync)) -> Value,
}

impl ListMatcherWrapper {
    fn eq_any<T: Any + PartialEq + Send + Sync>(
        t1: &(dyn Any + Send + Sync),
        t2: &(dyn Any + Send + Sync),
    ) -> bool {
        let t1 = t1.downcast_ref::<T>().unwrap();
        match t2.downcast_ref::<T>() {
            Some(t2) => t1.eq(t2),
            None => false,
        }
    }

    fn fmt_any<T: Any + Debug + Send + Sync>(
        t: &(dyn Any + Send + Sync),
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        t.downcast_ref::<T>().unwrap().fmt(f)
    }

    fn match_any<T: Any + ListMatcher + Send + Sync>(
        t: &(dyn Any + Send + Sync),
        list_name: &str,
        v: &LhsValue<'_>,
    ) -> bool {
        t.downcast_ref::<T>().unwrap().match_value(list_name, v)
    }

    #[allow(clippy::wrong_self_convention)]
    fn to_json_value_any<T: Any + ListMatcher + Send + Sync>(t: &(dyn Any + Send + Sync)) -> Value {
        t.downcast_ref::<T>().unwrap().to_json_value()
    }

    /// Creates a new ListMatcherWrapper object containing user-defined  object of type `T`
    pub fn new<T: Any + Clone + Debug + PartialEq + ListMatcher + Send + Sync>(t: T) -> Self {
        Self {
            inner: Box::new(t),
            eq_cb: Self::eq_any::<T>,
            fmt_cb: Self::fmt_any::<T>,
            match_cb: Self::match_any::<T>,
            to_json_value_cb: Self::to_json_value_any::<T>,
        }
    }
}

impl<T: Any> std::convert::AsRef<T> for ListMatcherWrapper {
    fn as_ref(&self) -> &T {
        self.inner.downcast_ref::<T>().unwrap()
    }
}

impl<T: Any> std::convert::AsMut<T> for ListMatcherWrapper {
    fn as_mut(&mut self) -> &mut T {
        self.inner.downcast_mut::<T>().unwrap()
    }
}

impl std::fmt::Debug for ListMatcherWrapper {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ListMatcherWrapper(")?;
        (self.fmt_cb)(&*self.inner, f)?;
        write!(f, ")")?;
        Ok(())
    }
}

impl Eq for ListMatcherWrapper {}

impl PartialEq for ListMatcherWrapper {
    fn eq(&self, other: &Self) -> bool {
        (self.eq_cb)(&*self.inner, &*other.inner)
    }
}

impl ListMatcher for ListMatcherWrapper {
    fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool {
        (self.match_cb)(&*self.inner, list_name, val)
    }

    fn to_json_value(&self) -> Value {
        (self.to_json_value_cb)(&*self.inner)
    }
}

/// List that always matches.
#[derive(Debug, Default)]
pub struct AlwaysList {}

/// Matcher for `AlwaysList`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct AlwaysListMatcher {}

impl ListDefinition for AlwaysList {
    fn matcher_from_json_value(
        &self,
        _: Type,
        _: serde_json::Value,
    ) -> Result<ListMatcherWrapper, serde_json::Error> {
        Ok(ListMatcherWrapper::new(AlwaysListMatcher {}))
    }

    fn is_valid_matcher(&self, matcher: &dyn Any) -> bool {
        matcher.is::<AlwaysListMatcher>()
    }
}

impl ListMatcher for AlwaysListMatcher {
    fn match_value(&self, _: &str, _: &LhsValue<'_>) -> bool {
        false
    }

    fn to_json_value(&self) -> serde_json::Value {
        serde_json::Value::Null
    }
}

/// List that never matches.
#[derive(Debug, Default)]
pub struct NeverList {}

/// Matcher for `NeverList`
#[derive(Clone, Debug, Default, PartialEq)]
pub struct NeverListMatcher {}

impl ListDefinition for NeverList {
    fn matcher_from_json_value(
        &self,
        _: Type,
        _: serde_json::Value,
    ) -> Result<ListMatcherWrapper, serde_json::Error> {
        Ok(ListMatcherWrapper::new(NeverListMatcher {}))
    }

    fn is_valid_matcher(&self, matcher: &dyn Any) -> bool {
        matcher.is::<NeverListMatcher>()
    }
}

impl ListMatcher for NeverListMatcher {
    fn match_value(&self, _: &str, _: &LhsValue<'_>) -> bool {
        false
    }

    fn to_json_value(&self) -> serde_json::Value {
        serde_json::Value::Null
    }
}
