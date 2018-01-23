use libc::size_t;
use std::{slice, str};

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Array<'a, T: 'a> {
    data: &'a T,
    length: size_t,
}

impl<'a, T: 'a> Array<'a, T> {
    pub fn as_slice(self) -> &'a [T] {
        unsafe { slice::from_raw_parts(self.data, self.length) }
    }
}

impl<T> From<Box<[T]>> for Array<'static, T> {
    fn from(raw: Box<[T]>) -> Self {
        let raw = Box::into_raw(raw);
        unsafe {
            Array {
                data: &*((*raw).as_ptr()),
                length: (*raw).len(),
            }
        }
    }
}

impl<T> From<Vec<T>> for Array<'static, T> {
    fn from(raw: Vec<T>) -> Self {
        Array::from(raw.into_boxed_slice())
    }
}

impl<T> Array<'static, T> {
    pub unsafe fn free(self) {
        Box::from_raw(slice::from_raw_parts_mut(
            self.data as *const T as *mut T,
            self.length,
        ));
    }
}

pub type Str<'a> = Array<'a, u8>;

impl<'a> Str<'a> {
    pub fn as_str(self) -> Result<&'a str, str::Utf8Error> {
        str::from_utf8(self.as_slice())
    }
}

impl From<Box<str>> for Str<'static> {
    fn from(raw: Box<str>) -> Self {
        Str::from(raw.into_boxed_bytes())
    }
}

impl From<String> for Str<'static> {
    fn from(raw: String) -> Self {
        Str::from(raw.into_boxed_str())
    }
}
