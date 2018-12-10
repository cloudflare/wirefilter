use super::ExternPtrRepr;
use libc::size_t;
use std::slice;

/// This structure provides FFI-safe representation for Rust slice pointers
/// by splitting them into data and length parts.
///
/// Example C definition for `ExternSliceRepr<u8>`:
/// ```
/// struct ByteSlice {
///     const uint8_t *data;
///     size_t length;
/// };
/// ```
#[repr(C)]
pub struct ExternSliceRepr<T> {
    data: *mut T,
    length: size_t,
}

// Can't be derived without bound on `T: Clone`.
impl<T> Clone for ExternSliceRepr<T> {
    fn clone(&self) -> Self {
        ExternSliceRepr {
            data: self.data,
            length: self.length,
        }
    }
}

impl<T> Copy for ExternSliceRepr<T> {}

impl<T> From<*mut [T]> for ExternSliceRepr<T> {
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    fn from(ptr: *mut [T]) -> Self {
        unsafe {
            ExternSliceRepr {
                data: (*ptr).as_mut_ptr(),
                length: (*ptr).len(),
            }
        }
    }
}

impl<T> ExternPtrRepr for [T] {
    type Repr = ExternSliceRepr<T>;

    unsafe fn from_extern_repr_unchecked(repr: Self::Repr) -> *mut [T] {
        slice::from_raw_parts_mut(repr.data, repr.length)
    }

    fn from_extern_repr(repr: Self::Repr) -> *mut [T] {
        // `slice::from_raw_parts{_mut}` require data part to be non-null.
        if repr.data.is_null() {
            &mut []
        } else {
            unsafe { Self::from_extern_repr_unchecked(repr) }
        }
    }
}
