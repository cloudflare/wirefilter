use crate::{Compare, ContextFamily, LhsValue};
use memchr::memmem::{Finder, FinderBuilder};
use sliceslice::MemchrSearcher;

pub struct EmptySearcher;

impl<U: 'static, F: ContextFamily<UserData = U>> Compare<U, F> for EmptySearcher {
    #[inline]
    fn compare<'e, 'data: 'e>(&self, _: &LhsValue<'e>, _: &'e F::Context<'data>) -> bool {
        true
    }

    #[inline]
    fn compare_bytes<'e, 'data: 'e>(&self, _: &'e [u8], _: &'e F::Context<'data>) -> bool {
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

impl<U: 'static, F: ContextFamily<UserData = U>> Compare<U, F> for MemmemSearcher {
    #[inline]
    fn compare<'e, 'data: 'e>(&self, value: &LhsValue<'e>, _: &'e F::Context<'data>) -> bool {
        self.0
            .find(match value {
                LhsValue::Bytes(bytes) => bytes,
                _ => unreachable!(),
            })
            .is_some()
    }

    #[inline]
    fn compare_bytes<'e, 'data: 'e>(&self, value: &'e [u8], _: &'e F::Context<'data>) -> bool {
        self.0.find(value).is_some()
    }
}

impl<U: 'static, F: ContextFamily<UserData = U>> Compare<U, F> for MemchrSearcher {
    #[inline]
    fn compare<'e, 'data: 'e>(&self, value: &LhsValue<'e>, _: &'e F::Context<'data>) -> bool {
        self.search_in(match value {
            LhsValue::Bytes(bytes) => bytes,
            _ => unreachable!(),
        })
    }

    #[inline]
    fn compare_bytes<'e, 'data: 'e>(&self, value: &'e [u8], _: &'e F::Context<'data>) -> bool {
        self.search_in(value)
    }
}
