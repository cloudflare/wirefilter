use super::{ExternPtrRepr, ExternSliceRepr};
use std::str;

/// This structure provides FFI-safe representation for Rust string slice
/// pointers.
///
/// The representation is guaranteed to be the same as [`ExternSliceRepr`]
/// for regular bytes ([`u8`]), but adds extra conversion checks for UTF-8.
///
/// Example C definition:
/// ```
/// struct Str {
///     const uint8_t *data;
///     size_t length;
/// };
/// ```
#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct ExternStrRepr(ExternSliceRepr<u8>);

impl From<*mut str> for ExternStrRepr {
    #[cfg_attr(feature = "cargo-clippy", allow(not_unsafe_ptr_arg_deref))]
    fn from(ptr: *mut str) -> Self {
        let bytes: *mut [u8] = unsafe { (*ptr).as_bytes_mut() };
        ExternStrRepr(bytes.into())
    }
}

impl ExternPtrRepr for str {
    type Repr = ExternStrRepr;

    unsafe fn from_extern_repr_unchecked(repr: Self::Repr) -> *mut str {
        let bytes = ExternPtrRepr::from_extern_repr_unchecked(repr.0);
        str::from_utf8_unchecked_mut(&mut *bytes)
    }

    fn from_extern_repr(repr: Self::Repr) -> *mut str {
        let bytes = ExternPtrRepr::from_extern_repr(repr.0);
        // Make sure that strings coming via FFI are UTF-8 compatible.
        str::from_utf8_mut(unsafe { &mut *bytes }).unwrap()
    }
}
