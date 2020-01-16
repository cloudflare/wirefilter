mod slice;
mod str;

pub use self::{slice::ExternSliceRepr, str::ExternStrRepr};

/// This trait allows to define FFI-safe representation for fat pointers
/// with corresponding conversions.
///
/// Later this trait can be used by higher-level wrappers like
/// [`::transfer_types::RustBox`] and [`::transfer_types::Ref`] to add required
/// ownership semantics while preserving FFI compatibility.
pub trait ExternPtrRepr {
    type Repr: Copy + From<*mut Self>;

    /// # Safety
    ///
    /// This method will be used in places where data behind the pointer
    /// was allocated by Rust side, so implementors may omit potentially
    /// expensive safety checks.
    ///
    /// # Safety
    ///
    /// This function should not be called for objects allocated outside of Rust code.
    unsafe fn from_extern_repr_unchecked(repr: Self::Repr) -> *mut Self;

    /// This method will be used for pointers to data allocated by the FFI
    /// caller, and, when converting to a Rust pointer, must make sure that
    /// such conversion won't lead to Undefined Behaviour (e.g. check that
    /// slices don't have nullable data part and strings are valid UTF-8).
    fn from_extern_repr(repr: Self::Repr) -> *mut Self;
}

/// This is a blanket implementation for pointer to regular sized types.
/// They are already guaranteed to be thin and FFI-safe.
impl<T> ExternPtrRepr for T {
    type Repr = *mut T;

    unsafe fn from_extern_repr_unchecked(repr: Self::Repr) -> *mut Self {
        repr
    }

    fn from_extern_repr(repr: Self::Repr) -> *mut Self {
        repr
    }
}
