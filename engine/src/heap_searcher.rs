use memmem::{Searcher, TwoWaySearcher};
use std::marker::PhantomPinned;
use std::pin::Pin;
use std::ptr::NonNull;

/// A version of [`TwoWaySearcher`] that owns the needle data.
pub struct HeapSearcher {
    bytes: Box<[u8]>,
    inner: Option<TwoWaySearcher<'static>>,
    _pin: PhantomPinned,
}

impl HeapSearcher {
    pub fn new(bytes: impl Into<Box<[u8]>>) -> Pin<Box<Self>> {
        // NOTE: first put bytes into the structure and pin them all together
        // on the heap.
        let mut heap_searcher = Box::pin(HeapSearcher {
            bytes: bytes.into(),
            inner: None,
            _pin: PhantomPinned,
        });

        // NOTE: obtain a pointer for pinned bytes and create a pin
        // for the mutable reference of the searcher. This can be later
        // used in `Pin::get_unchecked_mut` which consumes the pin.
        let bytes = NonNull::from(&heap_searcher.bytes);
        let mut_pin = heap_searcher.as_mut();

        unsafe {
            let inner = TwoWaySearcher::new(&*bytes.as_ptr());

            Pin::get_unchecked_mut(mut_pin).inner = Some(inner);
        }

        heap_searcher
    }
}

impl Searcher for HeapSearcher {
    fn search_in(&self, haystack: &[u8]) -> Option<usize> {
        self.inner.as_ref().unwrap().search_in(haystack)
    }
}
