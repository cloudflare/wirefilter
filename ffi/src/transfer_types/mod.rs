pub mod raw_ptr_repr;

mod ownership_repr;
pub use self::ownership_repr::{Ref, RustBox};

pub type RustAllocatedString = RustBox<str>;
pub type ExternallyAllocatedStr<'a> = Ref<'a, str>;
pub type ExternallyAllocatedByteArr<'a> = Ref<'a, [u8]>;
pub type StaticRustAllocatedString = Ref<'static, str>;
