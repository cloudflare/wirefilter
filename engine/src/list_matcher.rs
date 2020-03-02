use crate::LhsValue;
use std::any::Any;
use std::fmt::Debug;

/// Implement this Trait to match a given `LhsValue` against a list.
pub trait ListMatcher {
    /// Returns true if `val` is in the given list.
    fn match_value(&self, list_name: &str, val: &LhsValue) -> bool;
}

/// Wrapper to ensure that any ListMatcher implements the required Traits.
pub struct ListMatcherWrapper {
    inner: Box<dyn Any + Send + Sync>,
    clone_cb: fn(&(dyn Any + Send + Sync)) -> Box<dyn Any + Send + Sync>,
    eq_cb: fn(&(dyn Any + Send + Sync), &(dyn Any + Send + Sync)) -> bool,
    fmt_cb: fn(&(dyn Any + Send + Sync), &mut std::fmt::Formatter<'_>) -> std::fmt::Result,
    match_cb: fn(&(dyn Any + Send + Sync), &str, &LhsValue) -> bool,
}

impl ListMatcherWrapper {
    fn clone_any<T: Any + Clone + Send + Sync>(
        t: &(dyn Any + Send + Sync),
    ) -> Box<dyn Any + Send + Sync> {
        Box::new(t.downcast_ref::<T>().unwrap().clone())
    }

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
        v: &LhsValue,
    ) -> bool {
        t.downcast_ref::<T>().unwrap().match_value(list_name, v)
    }

    /// Creates a new ListMatcherWrapper object containing user-defined  object of type `T`
    pub fn new<T: Any + Clone + Debug + PartialEq + ListMatcher + Send + Sync>(t: T) -> Self {
        Self {
            inner: Box::new(t),
            clone_cb: Self::clone_any::<T>,
            eq_cb: Self::eq_any::<T>,
            fmt_cb: Self::fmt_any::<T>,
            match_cb: Self::match_any::<T>,
        }
    }
    /// Returns a reference to the underlying Any object
    pub fn as_any_ref(&self) -> &(dyn Any + Send + Sync) {
        &*self.inner
    }
    /// Returns a mutable reference to the underlying Any object
    pub fn as_any_mut(&mut self) -> &mut (dyn Any + Send + Sync) {
        &mut *self.inner
    }
    /// Converts current `ListMatcherWrapper` to `Box<dyn Dy>`
    pub fn into_any(self) -> Box<dyn Any + Send + Sync> {
        let Self { inner, .. } = self;
        inner
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

impl Clone for ListMatcherWrapper {
    fn clone(&self) -> Self {
        Self {
            inner: (self.clone_cb)(&*self.inner),
            clone_cb: self.clone_cb,
            eq_cb: self.eq_cb,
            fmt_cb: self.fmt_cb,
            match_cb: self.match_cb,
        }
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
    fn match_value(&self, list_name: &str, val: &LhsValue) -> bool {
        (self.match_cb)(&*self.inner, list_name, val)
    }
}
