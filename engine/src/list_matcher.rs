use crate::{LhsValue, Type};
use dyn_clone::DynClone;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fmt::Debug;

/// Defines a new list to match against.
///
/// `ListDefinition` needs to be registered in the `Scheme` for a given `Type`.
/// See `Scheme::add_list`.
pub trait ListDefinition: Debug + Sync + Send {
    /// Deserializes a list matcher.
    ///
    /// This method is necessary to support deserialization of lists during the
    /// the deserialization of an `ExecutionContext`.
    fn deserialize_matcher(
        &self,
        ty: Type,
        deserializer: &mut dyn erased_serde::Deserializer<'_>,
    ) -> Result<Box<dyn ListMatcher>, erased_serde::Error>;

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

/// Implement this trait to match a given `LhsValue` against a list.
pub trait ListMatcher:
    AsAny + Debug + DynClone + DynPartialEq + Send + Sync + erased_serde::Serialize + 'static
{
    /// Returns true if `val` is in the given list.
    fn match_value(&self, list_name: &str, val: &LhsValue<'_>) -> bool;

    /// Clears the list matcher, removing all its content.
    fn clear(&mut self);
}

dyn_clone::clone_trait_object!(ListMatcher);

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
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlwaysListMatcher {}

impl ListDefinition for AlwaysList {
    fn deserialize_matcher(
        &self,
        _: Type,
        deserializer: &mut dyn erased_serde::Deserializer<'_>,
    ) -> Result<Box<dyn ListMatcher>, erased_serde::Error> {
        let matcher = erased_serde::deserialize::<AlwaysListMatcher>(deserializer)?;
        Ok(Box::new(matcher))
    }

    fn new_matcher(&self) -> Box<dyn ListMatcher> {
        Box::new(AlwaysListMatcher {})
    }
}

impl ListMatcher for AlwaysListMatcher {
    fn match_value(&self, _: &str, _: &LhsValue<'_>) -> bool {
        false
    }

    fn clear(&mut self) {}
}

/// List that never matches.
#[derive(Debug, Default)]
pub struct NeverList {}

/// Matcher for `NeverList`
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct NeverListMatcher {}

impl ListDefinition for NeverList {
    fn deserialize_matcher(
        &self,
        _: Type,
        deserializer: &mut dyn erased_serde::Deserializer<'_>,
    ) -> Result<Box<dyn ListMatcher>, erased_serde::Error> {
        let matcher = erased_serde::deserialize::<NeverListMatcher>(deserializer)?;
        Ok(Box::new(matcher))
    }

    fn new_matcher(&self) -> Box<dyn ListMatcher> {
        Box::new(NeverListMatcher {})
    }
}

impl ListMatcher for NeverListMatcher {
    fn match_value(&self, _: &str, _: &LhsValue<'_>) -> bool {
        false
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
