use super::{ExternPtrRepr, ExternPtrReprMut};
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
    data: *const T,
    length: size_t,
}

// Can't be derived without bound on `T: Clone`.
impl<T> Clone for ExternSliceRepr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for ExternSliceRepr<T> {}

impl<T> From<*const [T]> for ExternSliceRepr<T> {
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    fn from(ptr: *const [T]) -> Self {
        unsafe {
            ExternSliceRepr {
                data: (*ptr).as_ptr(),
                length: (*ptr).len(),
            }
        }
    }
}

impl<T> ExternPtrRepr for [T] {
    type Repr = ExternSliceRepr<T>;

    unsafe fn from_extern_repr_unchecked(repr: Self::Repr) -> *const [T] {
        slice::from_raw_parts(repr.data, repr.length)
    }

    fn from_extern_repr(repr: Self::Repr) -> *const [T] {
        // `slice::from_raw_parts{_mut}` require data part to be non-null.
        if repr.data.is_null() {
            &[]
        } else {
            unsafe { ExternPtrRepr::from_extern_repr_unchecked(repr) }
        }
    }
}

#[repr(C)]
pub struct ExternSliceReprMut<T> {
    data: *mut T,
    length: size_t,
}

// Can't be derived without bound on `T: Clone`.
impl<T> Clone for ExternSliceReprMut<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for ExternSliceReprMut<T> {}

impl<T> From<*mut [T]> for ExternSliceReprMut<T> {
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    fn from(ptr: *mut [T]) -> Self {
        unsafe {
            ExternSliceReprMut {
                data: (*ptr).as_mut_ptr(),
                length: (*ptr).len(),
            }
        }
    }
}

impl<T> ExternPtrReprMut for [T] {
    type Repr = ExternSliceReprMut<T>;

    unsafe fn from_extern_repr_unchecked(repr: Self::Repr) -> *mut [T] {
        slice::from_raw_parts_mut(repr.data, repr.length)
    }

    fn from_extern_repr(repr: Self::Repr) -> *mut [T] {
        // `slice::from_raw_parts{_mut}` require data part to be non-null.
        if repr.data.is_null() {
            &mut []
        } else {
            unsafe { ExternPtrReprMut::from_extern_repr_unchecked(repr) }
        }
    }
}
