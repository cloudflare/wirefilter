use crate::transfer_types::raw_ptr_repr::ExternPtrRepr;
use std::{
    marker::PhantomData,
    mem,
    ops::{Deref, DerefMut},
};

#[derive(Debug)]
#[repr(transparent)]
pub struct RustBox<T: ?Sized + ExternPtrRepr> {
    ptr: T::Repr,
    ownership_marker: PhantomData<T>,
}

// We want to be able to move values out of `RustBox`, but this is something
// Rust compiler doesn't allow for custom types. However, it does allow this
// for real `Box` by treating it in a special manner, so we want to provide
// conversion to that real `Box` to unlock these features.
impl<T: ?Sized + ExternPtrRepr> RustBox<T> {
    // This needs to accept a reference not an owned version in order to work
    // inside of `Drop` implementation (and is highly unsafe otherwise).
    unsafe fn to_real_box_impl(&self) -> Box<T> {
        Box::from_raw(T::from_extern_repr_unchecked(self.ptr))
    }

    pub fn into_real_box(self) -> Box<T> {
        // Convert from the internal representation...
        let result = unsafe { self.to_real_box_impl() };
        // ...and forget the original to avoid double-free.
        mem::forget(self);
        result
    }
}

impl<T: ?Sized + ExternPtrRepr> Deref for RustBox<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*ExternPtrRepr::from_extern_repr_unchecked(self.ptr) }
    }
}

impl<T: ?Sized + ExternPtrRepr> DerefMut for RustBox<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *ExternPtrRepr::from_extern_repr_unchecked(self.ptr) }
    }
}

impl<T: ?Sized + ExternPtrRepr> From<Box<T>> for RustBox<T> {
    fn from(b: Box<T>) -> Self {
        RustBox {
            ptr: Box::into_raw(b).into(),
            ownership_marker: PhantomData,
        }
    }
}

impl<T> From<T> for RustBox<T> {
    fn from(value: T) -> Self {
        Box::new(value).into()
    }
}

impl<T: ?Sized + ExternPtrRepr> Drop for RustBox<T> {
    fn drop(&mut self) {
        drop(unsafe { self.to_real_box_impl() });
    }
}

impl<T: ?Sized + ExternPtrRepr> Default for RustBox<T>
where
    Box<T>: Default,
{
    fn default() -> Self {
        <Box<T>>::default().into()
    }
}

impl From<String> for RustBox<str> {
    fn from(s: String) -> Self {
        s.into_boxed_str().into()
    }
}
