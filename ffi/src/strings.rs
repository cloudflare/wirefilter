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
pub struct ExternallyAllocatedStr<'a> {
    data: &'a u8,
    length: size_t,
}

impl<'a> ExternallyAllocatedStr<'a> {
    fn as_str(&self) -> &'a str {
        let slice = unsafe { slice::from_raw_parts(self.data, self.length) };
        str::from_utf8(slice).unwrap()
    }
}

impl<'a> Into<&'a str> for ExternallyAllocatedStr<'a> {
    fn into(self) -> &'a str {
        self.as_str()
    }
}

impl<'a> Into<String> for ExternallyAllocatedStr<'a> {
    fn into(self) -> String {
        format!("{}", self.as_str())
    }
}

#[cfg(test)]
impl From<&'static str> for ExternallyAllocatedStr<'static> {
    fn from(raw: &'static str) -> Self {
        ExternallyAllocatedStr {
            data: unsafe { &*raw.as_ptr() },
            length: raw.len(),
        }
    }
}
