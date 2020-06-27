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
    ) -> Result<Box<dyn ListMatcher>, serde_json::Error>;

    /// Creates a new matcher object for this list.
    fn new_matcher(&self) -> Box<dyn ListMatcher>;
}

pub trait AsAny {
    fn as_any(&self) -> &dyn Any;

    fn as_any_mut(&mut self) -> &mut dyn Any;
}

impl<T: Any> AsAny for T {
    #[inline]
    fn as_any(&self) -> &dyn Any {
        self
    }

    #[inline]
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// Object safe version of PartialEq trait used for equality comparison.
pub trait DynPartialEq {
    fn dyn_eq(&self, other: &dyn Any) -> bool;
}

impl<T: PartialEq + Any> DynPartialEq for T {
    #[inline]
    fn dyn_eq(&self, other: &dyn Any) -> bool {
        if let Some(other) = other.downcast_ref::<Self>() {
            self == other
        } else {
            false
        }
    }
}

/// Implement this Trait to match a given `LhsValue` against a list.
pub trait ListMatcher: AsAny + Debug + DynPartialEq + Send + Sync + 'static {
    /// Returns true if `val` is in the given list.
    fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool;

    /// Convert the list matcher to a serde_json::Value in order to serialize it.
    fn to_json_value(&self) -> Value;

    /// Clears the list matcher, removing all its content.
    fn clear(&mut self);
}

impl PartialEq for dyn ListMatcher {
    #[inline]
    fn eq(&self, other: &dyn ListMatcher) -> bool {
        DynPartialEq::dyn_eq(self, other.as_any())
    }
}

/// List that always matches.
#[derive(Debug, Default)]
pub struct AlwaysList {}

/// Matcher for `AlwaysList`
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct AlwaysListMatcher {}

impl ListDefinition for AlwaysList {
    fn matcher_from_json_value(
        &self,
        _: Type,
        _: serde_json::Value,
    ) -> Result<Box<dyn ListMatcher>, serde_json::Error> {
        Ok(Box::new(AlwaysListMatcher {}))
    }

    fn new_matcher(&self) -> Box<dyn ListMatcher> {
        Box::new(AlwaysListMatcher {})
    }
}

impl ListMatcher for AlwaysListMatcher {
    fn match_value(&self, _: &str, _: &LhsValue<'_>) -> bool {
        false
    }

    fn to_json_value(&self) -> serde_json::Value {
        serde_json::Value::Null
    }

    fn clear(&mut self) {}
}

/// List that never matches.
#[derive(Debug, Default)]
pub struct NeverList {}

/// Matcher for `NeverList`
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct NeverListMatcher {}

impl ListDefinition for NeverList {
    fn matcher_from_json_value(
        &self,
        _: Type,
        _: serde_json::Value,
    ) -> Result<Box<dyn ListMatcher>, serde_json::Error> {
        Ok(Box::new(NeverListMatcher {}))
    }

    fn new_matcher(&self) -> Box<dyn ListMatcher> {
        Box::new(NeverListMatcher {})
    }
}

impl ListMatcher for NeverListMatcher {
    fn match_value(&self, _: &str, _: &LhsValue<'_>) -> bool {
        false
    }

    fn to_json_value(&self) -> serde_json::Value {
        serde_json::Value::Null
    }

    fn clear(&mut self) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list_matcher_wrapper_comparison() {
        let always_list_matcher: Box<dyn ListMatcher> = Box::new(AlwaysListMatcher {});

        let always_list_matcher_2: Box<dyn ListMatcher> = Box::new(AlwaysListMatcher {});

        assert_eq!(&always_list_matcher, &always_list_matcher_2);

        let never_list_matcher: Box<dyn ListMatcher> = Box::new(NeverListMatcher {});

        assert_ne!(&always_list_matcher, &never_list_matcher);

        assert_ne!(&always_list_matcher_2, &never_list_matcher);
    }
}
