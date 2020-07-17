use memmem::Searcher;
use std::mem::ManuallyDrop;

pub struct EmptySearcher;

impl EmptySearcher {
    #[inline]
    pub fn search_in(&self, _haystack: &[u8]) -> bool {
        true
    }
}

pub struct TwoWaySearcher {
    // This is an `Box` whose lifetime must exceed `searcher`.
    needle: ManuallyDrop<Box<[u8]>>,

    // We need this because `memmem::TwoWaySearcher` wants a lifetime for the data it refers to, but
    // we don't want to tie it to the lifetime of `TwoWaySearcher`, since our data is heap-allocated
    // and is guaranteed to deref to the same address across moves of the container. Hence, we use
    // `static` as a substitute lifetime and it points to the same the data as `needle`.
    searcher: ManuallyDrop<memmem::TwoWaySearcher<'static>>,
}

impl TwoWaySearcher {
    pub fn new(needle: Box<[u8]>) -> Self {
        // Convert needle's contents to the static lifetime.
        let needle_static = unsafe { &*(&*needle as *const [u8]) };

        TwoWaySearcher {
            needle: ManuallyDrop::new(needle),
            searcher: ManuallyDrop::new(memmem::TwoWaySearcher::new(needle_static)),
        }
    }

    #[inline]
    pub fn search_in(&self, haystack: &[u8]) -> bool {
        self.searcher.search_in(haystack).is_some()
    }
}

impl Drop for TwoWaySearcher {
    fn drop(&mut self) {
        unsafe {
            // Explicitly drop `searcher` first in case it needs `needle` to be alive.
            ManuallyDrop::drop(&mut self.searcher);
            ManuallyDrop::drop(&mut self.needle);
        }
    }
}
