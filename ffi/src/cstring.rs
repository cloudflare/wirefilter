use std::fmt::{self, Debug};
use std::io;
use std::os::raw::c_char;

/// Used for replacing null bytes in C strings that cannot contain null bytes.
const SUBSTITUTE_BYTE: u8 = 0x1a;

/// A type representing an owned, C-compatible, nul-terminated string with no
/// nul bytes in the middle.
///
/// It differs from [`std::ffi::CString`] in that it stores a `Vec<u8>`, rather
/// than a `Box<[u8]>`. This allows it to implement traits such as [`std::io::Write`].
#[derive(Debug, Default)]
pub struct CString(Vec<u8>);

impl CString {
    pub(crate) const fn new() -> Self {
        Self(Vec::new())
    }

    fn append(&mut self, buf: &[u8]) {
        self.0.pop();
        let len = self.0.len();
        self.0.extend(buf);
        let new_len = self.0.len();
        self.0[len..new_len].iter_mut().for_each(|b| {
            if *b == b'\0' {
                *b = SUBSTITUTE_BYTE;
            }
        });
        self.0.push(0u8);
    }

    /// Clears the contents of the string.
    #[inline]
    pub fn clear(&mut self) -> &mut Self {
        self.0.clear();
        self
    }

    /// Retrieves the string as a `*const c_char`.
    #[inline]
    pub fn as_c_str(&self) -> *const c_char {
        if self.0.is_empty() {
            std::ptr::null()
        } else {
            self.0.as_ptr() as *const c_char
        }
    }
}

impl io::Write for CString {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.append(buf);
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl fmt::Write for CString {
    fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
        self.append(s.as_bytes());
        Ok(())
    }
}
