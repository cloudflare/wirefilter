use std::marker::PhantomData;
use transfer_types::raw_ptr_repr::ExternPtrRepr;

#[repr(transparent)]
pub struct Ref<'a, T: ?Sized + ExternPtrRepr> {
    ptr: T::Repr,
    ownership_marker: PhantomData<&'a T>,
}

// We don't want to implement `Deref` because we want to perform
// potentially expensive checks and consume unsafe wrapper once.
impl<'a, T: ?Sized + ExternPtrRepr> Ref<'a, T> {
    pub fn into_ref(self) -> &'a T {
        let slice: *mut T = ExternPtrRepr::from_extern_repr(self.ptr);
        unsafe { &*slice }
    }
}

impl<'a, T: ?Sized + ExternPtrRepr> From<&'a T> for Ref<'a, T> {
    fn from(ptr: &'a T) -> Self {
        Ref {
            ptr: (ptr as *const T as *mut T).into(),
            ownership_marker: PhantomData,
        }
    }
}

impl<'a> From<&'a str> for Ref<'a, [u8]> {
    fn from(s: &'a str) -> Self {
        s.as_bytes().into()
    }
}
