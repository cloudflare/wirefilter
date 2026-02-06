use memchr::memmem::{Finder, FinderBuilder};
use sliceslice::MemchrSearcher;

use crate::{Compare, ExecutionContext, LhsValue};

pub struct EmptySearcher;

impl<U> Compare<U> for EmptySearcher {
    #[inline]
    fn compare<'e>(&self, _: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
        true
    }
}

pub struct MemmemSearcher(Finder<'static>);

impl MemmemSearcher {
    #[inline]
    pub fn new(needle: Box<[u8]>) -> Self {
        Self(FinderBuilder::new().build_forward_owned(needle))
    }
}

impl<U> Compare<U> for MemmemSearcher {
    #[inline]
    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
        self.0
            .find(match value {
                LhsValue::Bytes(bytes) => bytes,
                _ => unreachable!(),
            })
            .is_some()
    }
}

impl<U> Compare<U> for MemchrSearcher {
    #[inline]
    fn compare<'e>(&self, value: &LhsValue<'e>, _: &'e ExecutionContext<'e, U>) -> bool {
        self.search_in(match value {
            LhsValue::Bytes(bytes) => bytes,
            _ => unreachable!(),
        })
    }
}
