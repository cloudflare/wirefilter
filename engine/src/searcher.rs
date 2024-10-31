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
    needle: *mut [u8],

    // We need this because `memmem::TwoWaySearcher` wants a lifetime for the data it refers to, but
    // we don't want to tie it to the lifetime of `TwoWaySearcher`, since our data is heap-allocated
    // and is guaranteed to deref to the same address across moves of the container. Hence, we use
    // `static` as a substitute lifetime and it points to the same the data as `needle`.
    searcher: ManuallyDrop<memmem::TwoWaySearcher<'static>>,
}

// This is safe because we are only ever accessing `needle` mutably during `Drop::drop`
// which is statically enforced by the compiler to be called once when the searcher is
// not in used anymore.
unsafe impl Send for TwoWaySearcher {}
// This is safe because we are only ever accessing `needle` mutably during `Drop::drop`
// which is statically enforced by the compiler to be called once when the searcher is
// not in used anymore.
unsafe impl Sync for TwoWaySearcher {}

impl TwoWaySearcher {
    pub fn new(needle: Box<[u8]>) -> Self {
        let needle = Box::into_raw(needle);
        // Convert needle's contents to the static lifetime.
        let needle_static = unsafe { &*needle };

        TwoWaySearcher {
            needle,
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
            drop(Box::from_raw(self.needle));
        }
    }
}
