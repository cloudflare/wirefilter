use libc::size_t;
use std::{slice, str};

#[repr(C)]
pub struct RustAllocatedString {
    data: *const u8,
    length: size_t,
}

impl From<String> for RustAllocatedString {
    fn from(raw: String) -> Self {
        let bytes = raw.into_boxed_str().into_boxed_bytes();
        let raw = Box::into_raw(bytes);

        unsafe {
            RustAllocatedString {
                data: (*raw).as_ptr(),
                length: (*raw).len(),
            }
        }
    }
}

impl Drop for RustAllocatedString {
    fn drop(&mut self) {
        unsafe {
            let slice = slice::from_raw_parts_mut(self.data as *mut u8, self.length);
            Box::from_raw(slice);
        }
    }
}

#[cfg(test)]
impl RustAllocatedString {
    pub fn as_str(&self) -> &str {
        let slice = unsafe { slice::from_raw_parts(self.data, self.length) };
        str::from_utf8(slice).unwrap()
    }
}

#[repr(C)]
pub struct ExternallyAllocatedByteArr<'a> {
    data: &'a u8,
    length: size_t,
}

impl<'a> Into<&'a str> for ExternallyAllocatedByteArr<'a> {
    fn into(self) -> &'a str {
        str::from_utf8(self.into()).unwrap()
    }
}

impl<'a> Into<String> for ExternallyAllocatedByteArr<'a> {
    fn into(self) -> String {
        let slice: &'a str = self.into();
        slice.to_owned()
    }
}

impl<'a> Into<&'a [u8]> for ExternallyAllocatedByteArr<'a> {
    fn into(self) -> &'a [u8] {
        unsafe { slice::from_raw_parts(self.data, self.length) }
    }
}

#[cfg(test)]
impl From<&'static [u8]> for ExternallyAllocatedByteArr<'static> {
    fn from(raw: &'static [u8]) -> Self {
        ExternallyAllocatedByteArr {
            data: unsafe { &*raw.as_ptr() },
            length: raw.len(),
        }
    }
}

#[cfg(test)]
impl From<&'static str> for ExternallyAllocatedByteArr<'static> {
    fn from(raw: &'static str) -> Self {
        ExternallyAllocatedByteArr::from(raw.as_bytes())
    }
}
