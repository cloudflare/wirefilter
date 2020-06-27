use crate::CResult;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::panic::UnwindSafe;
use wirefilter::{
    panic_catcher_disable, panic_catcher_enable, panic_catcher_set_fallback_mode,
    panic_catcher_set_hook, PanicCatcherFallbackMode,
};

#[repr(u8)]
#[derive(Clone, Copy, IntoPrimitive, TryFromPrimitive)]
pub enum CPanicCatcherFallbackMode {
    Continue = 0u8,
    Abort = 1u8,
}

#[inline(always)]
pub(crate) fn catch_panic<F, T>(f: F) -> CResult<T>
where
    F: FnOnce() -> Result<T, String> + UnwindSafe,
{
    match wirefilter::catch_panic(f) {
        Ok(ok) => CResult::Ok(ok),
        Err(msg) => CResult::Err(msg.into()),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_set_panic_catcher_hook() {
    panic_catcher_set_hook()
}

#[no_mangle]
pub extern "C" fn wirefilter_set_panic_catcher_fallback_mode(fallback_mode: u8) -> CResult<bool> {
    let fallback_mode = match fallback_mode {
        0 => PanicCatcherFallbackMode::Continue,
        1 => PanicCatcherFallbackMode::Abort,
        _ => return CResult::Err(format!("Invalid fallback mode {fallback_mode}").into()),
    };

    panic_catcher_set_fallback_mode(fallback_mode);
    CResult::Ok(true)
}

#[no_mangle]
pub extern "C" fn wirefilter_enable_panic_catcher() {
    panic_catcher_enable()
}

#[no_mangle]
pub extern "C" fn wirefilter_disable_panic_catcher() {
    panic_catcher_disable()
}

#[cfg(test)]
mod panic_test {
    use super::*;
    use crate::CResult;

    #[test]
    #[cfg_attr(miri, ignore)]
    #[should_panic(expected = r#"Hello World!"#)]
    fn test_panic_catcher_set_panic_hook_can_still_panic() {
        wirefilter_set_panic_catcher_hook();
        panic!("Hello World!");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[should_panic(expected = r#"Hello World!"#)]
    fn test_panic_catcher_enabled_disabled_can_still_panic() {
        wirefilter_set_panic_catcher_hook();
        wirefilter_enable_panic_catcher();
        wirefilter_disable_panic_catcher();
        panic!("Hello World!");
    }

    #[test]
    fn test_panic_catcher_can_catch_panic() {
        wirefilter_set_panic_catcher_hook();
        wirefilter_set_panic_catcher_fallback_mode(1).unwrap();
        wirefilter_enable_panic_catcher();
        let result: CResult<()> = catch_panic(|| panic!("Halt and Catch Panic"));
        match result {
            CResult::Ok(_) => unreachable!(),
            CResult::Err(msg) => assert!(msg.contains("Halt and Catch Panic")),
        }
        wirefilter_disable_panic_catcher();
    }
}
