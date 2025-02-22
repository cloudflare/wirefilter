use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::fmt::Write;
use wirefilter::{
    PanicCatcherFallbackMode, panic_catcher_disable, panic_catcher_enable,
    panic_catcher_set_fallback_mode, panic_catcher_set_hook,
};

#[repr(u8)]
#[derive(Clone, Copy, IntoPrimitive, TryFromPrimitive)]
pub enum CPanicCatcherFallbackMode {
    Continue = 0u8,
    Abort = 1u8,
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_set_panic_catcher_hook() {
    panic_catcher_set_hook()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_set_panic_catcher_fallback_mode(fallback_mode: u8) -> bool {
    let fallback_mode = match fallback_mode {
        0 => PanicCatcherFallbackMode::Continue,
        1 => PanicCatcherFallbackMode::Abort,
        _ => {
            crate::write_last_error!("Invalid fallback mode {fallback_mode}");
            return false;
        }
    };

    panic_catcher_set_fallback_mode(fallback_mode);
    true
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_enable_panic_catcher() {
    panic_catcher_enable()
}

#[unsafe(no_mangle)]
pub extern "C" fn wirefilter_disable_panic_catcher() {
    panic_catcher_disable()
}

#[cfg(test)]
mod panic_test {
    use super::*;

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
        assert!(wirefilter_set_panic_catcher_fallback_mode(1));
        wirefilter_enable_panic_catcher();
        let result = wirefilter::catch_panic(|| panic!("Halt and Catch Panic"));
        match result {
            Ok(_) => unreachable!(),
            Err(err) => {
                assert!(err.to_string().contains("Halt and Catch Panic"));
            }
        }
        wirefilter_disable_panic_catcher();
    }
}
