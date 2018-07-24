use memmem::{Searcher, TwoWaySearcher};
use rhs_types::Bytes;
use std::{
    fmt::{self, Debug},
    hash::{Hash, Hasher},
};

#[derive(Clone)]
pub struct ContainsOp {
    bytes: Bytes,

    // We need this because `TwoWaySearcher` wants a lifetime for the data it
    // refers to, but we don't really want to propagate this lifetime throughout
    // `ContainsOp` and all its parent data structures. Instead, we use `'static`
    // as a substitute lifetime, point `searcher` to the heap-allocated data
    // and make sure that `bytes` (actual owner of that heap-allocated data)
    // is not moved/dropped out of the structure while we still need it by
    // simply not exposing it to public, so both properties are alive as long
    // as structure itself is.
    searcher: TwoWaySearcher<'static>,
}

impl<T: Into<Bytes>> From<T> for ContainsOp {
    fn from(bytes: T) -> ContainsOp {
        let bytes = bytes.into();
        // Magic to convert &Bytes to &[u8] and then unbind lifetime to 'static
        // (see comment above to understand why).
        let heap_ref = unsafe { &*(&bytes[..] as *const _) };
        ContainsOp {
            bytes,
            searcher: TwoWaySearcher::new(heap_ref),
        }
    }
}

impl PartialEq for ContainsOp {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl Eq for ContainsOp {}

impl Hash for ContainsOp {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.bytes.hash(h)
    }
}

impl Debug for ContainsOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.bytes.fmt(f)
    }
}

impl Searcher for ContainsOp {
    fn search_in(&self, haystack: &[u8]) -> Option<usize> {
        self.searcher.search_in(haystack)
    }
}
