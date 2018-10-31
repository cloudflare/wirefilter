use memmem::{Searcher, TwoWaySearcher};
use std::mem::ManuallyDrop;

pub struct HeapSearcher {
    // This is an unwrapped `Box` (pointer to a heap-allocated data).
    bytes: *mut [u8],

    // We need this because `TwoWaySearcher` wants a lifetime for the data it
    // refers to, but we don't want to tie it to the lifetime of `HeapSearcher`,
    // since our data is heap-allocated and is guaranteed to deref to the same
    // address across moves of the container. Hence, we use `static` as a
    // substitute lifetime and it points to the same the data as `bytes`.
    searcher: ManuallyDrop<TwoWaySearcher<'static>>,
}

impl<T: Into<Box<[u8]>>> From<T> for HeapSearcher {
    fn from(bytes: T) -> HeapSearcher {
        let bytes = Box::leak(bytes.into());

        HeapSearcher {
            bytes,
            searcher: ManuallyDrop::new(TwoWaySearcher::new(bytes)),
        }
    }
}

impl Drop for HeapSearcher {
    fn drop(&mut self) {
        unsafe {
            // Explicitly drop `searcher` first in case it needs `bytes` to be alive.
            ManuallyDrop::drop(&mut self.searcher);
            // Then, wrap `bytes` pointer back into a `Box` and drop it too.
            drop(Box::from_raw(self.bytes));
        }
    }
}

impl Searcher for HeapSearcher {
    fn search_in(&self, haystack: &[u8]) -> Option<usize> {
        self.searcher.search_in(haystack)
    }
}
