use memmem::{Searcher, TwoWaySearcher};
use std::marker::PhantomPinned;
use std::pin::Pin;
use std::ptr::NonNull;

/// A version of [`TwoWaySearcher`] that owns the needle data.
pub struct HeapSearcher {
    // This is an `Box` whose lifetime must exceed `searcher`.
    bytes: ManuallyDrop<Box<[u8]>>,

    // We need this because `TwoWaySearcher` wants a lifetime for the data it
    // refers to, but we don't want to tie it to the lifetime of `HeapSearcher`,
    // since our data is heap-allocated and is guaranteed to deref to the same
    // address across moves of the container. Hence, we use `static` as a
    // substitute lifetime and it points to the same the data as `bytes`.
    searcher: ManuallyDrop<TwoWaySearcher<'static>>,
}

impl<T: Into<Box<[u8]>>> From<T> for HeapSearcher {
    fn from(bytes: T) -> HeapSearcher {
        let bytes_box = bytes.into();
        // Convert bytes' contents to the static lifetime.
        let bytes = unsafe { &*(&*bytes_box as *const [u8]) };

        HeapSearcher {
            bytes: ManuallyDrop::new(bytes_box),
            searcher: ManuallyDrop::new(TwoWaySearcher::new(bytes)),
        }
    }
}

        unsafe {
            // Explicitly drop `searcher` first in case it needs `bytes` to be alive.
            ManuallyDrop::drop(&mut self.searcher);
            // Then, drop `bytes`.
            ManuallyDrop::drop(&mut self.bytes);
        }

        heap_searcher
    }
}

impl Searcher for HeapSearcher {
    fn search_in(&self, haystack: &[u8]) -> Option<usize> {
        self.inner.as_ref().unwrap().search_in(haystack)
    }
}
