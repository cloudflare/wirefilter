use crate::transfer_types::RustAllocatedString;
use crate::CResult;
use num_enum::{IntoPrimitive, TryFromPrimitive};
use std::cell::{Cell, RefCell};
use std::convert::TryFrom;
use std::io::{self, Write};
use std::panic::UnwindSafe;
use std::sync::atomic::{AtomicBool, Ordering};

#[repr(u8)]
#[derive(Clone, Copy, IntoPrimitive, TryFromPrimitive)]
pub enum PanicCatcherFallbackMode {
    Continue,
    Abort,
}

thread_local! {
    // String to store last backtrace that is recorded in the panic catcher hook
    static PANIC_CATCHER_BACKTRACE : RefCell<String> = RefCell::new(String::new());

    // Boolean to check if we are currently trying to catch a pnic
    static PANIC_CATCHER_CATCH: Cell<bool> = Cell::new(false);

    // Fallback mode for when the hook is set but a panic occurs outside of a catch block
    static PANIC_CATCHER_FALLBACK_MODE: Cell<PanicCatcherFallbackMode> = Cell::new(PanicCatcherFallbackMode::Continue);

    // Status of the panic catcher
    static PANIC_CATCHER_ENABLED: Cell<bool> = Cell::new(false);
}
static PANIC_CATCHER_HOOK_SET: AtomicBool = AtomicBool::new(false);

pub fn panic_catcher_start_catching() -> bool {
    if PANIC_CATCHER_ENABLED.with(|b| b.get()) {
        PANIC_CATCHER_CATCH.with(|b| b.set(true));
        true
    } else {
        false
    }
}

pub fn panic_catcher_stop_catching() {
    PANIC_CATCHER_CATCH.with(|b| b.set(false));
}

pub fn panic_catcher_get_backtrace() -> Option<String> {
    PANIC_CATCHER_BACKTRACE.with(|bt| {
        let bt = bt.borrow();
        if bt.is_empty() {
            None
        } else {
            Some(bt.to_string())
        }
    })
}

#[inline(always)]
pub fn catch_panic<F, T>(f: F) -> CResult<T>
where
    F: FnOnce() -> CResult<T> + UnwindSafe,
{
    if panic_catcher_start_catching() {
        let result = std::panic::catch_unwind(f);
        panic_catcher_stop_catching();
        match result {
            Ok(res) => res,
            Err(_) => CResult::<T>::Err(RustAllocatedString::from(
                panic_catcher_get_backtrace().unwrap_or_else(|| {
                    "thread '<unknown>' panicked at '<unknown>' in file '<unknown>' at line 0"
                        .to_string()
                }),
            )),
        }
    } else {
        f()
    }
}

fn record_backtrace(info: &std::panic::PanicInfo, bt: &mut String) {
    let (file, line) = if let Some(location) = info.location() {
        (location.file(), location.line())
    } else {
        ("<unknown>", 0)
    };
    let payload = if let Some(payload) = info.payload().downcast_ref::<&str>() {
        payload
    } else if let Some(payload) = info.payload().downcast_ref::<String>() {
        payload
    } else {
        "<unknown>"
    };
    bt.truncate(0);
    let _ = std::fmt::write(
        &mut *bt,
        format_args!(
            "thread '{}' panicked at '{}' in file '{}' at line {}\n{:?}\n",
            std::thread::current().name().unwrap_or("<unknown>"),
            payload,
            file,
            line,
            backtrace::Backtrace::new()
        ),
    );
}

#[no_mangle]
pub extern "C" fn wirefilter_set_panic_catcher_hook() {
    if PANIC_CATCHER_HOOK_SET.load(Ordering::SeqCst) {
        return;
    }
    let next = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if PANIC_CATCHER_CATCH.with(|enabled| enabled.get()) {
            PANIC_CATCHER_BACKTRACE.with(|bt| {
                let mut bt = bt.borrow_mut();
                record_backtrace(info, &mut bt);
            });
            return;
        }
        match PANIC_CATCHER_FALLBACK_MODE.with(|b| b.get()) {
            PanicCatcherFallbackMode::Continue => next(info),
            PanicCatcherFallbackMode::Abort => {
                let mut bt = String::new();
                record_backtrace(info, &mut bt);
                let _ = io::stderr().write_all(bt.as_bytes());
                std::process::abort();
            }
        }
    }));
    PANIC_CATCHER_HOOK_SET.store(true, Ordering::SeqCst);
}

#[no_mangle]
pub extern "C" fn wirefilter_set_panic_catcher_fallback_mode(fallback_mode: u8) -> CResult<bool> {
    match PanicCatcherFallbackMode::try_from(fallback_mode) {
        Ok(fallback_mode) => {
            PANIC_CATCHER_FALLBACK_MODE.with(|b| b.set(fallback_mode));
            CResult::Ok(true)
        }
        Err(err) => CResult::Err(err.to_string().into()),
    }
}

#[no_mangle]
pub extern "C" fn wirefilter_enable_panic_catcher() {
    PANIC_CATCHER_ENABLED.with(|b| b.set(true));
}

#[no_mangle]
pub extern "C" fn wirefilter_disable_panic_catcher() {
    PANIC_CATCHER_ENABLED.with(|b| b.set(false));
}

#[cfg(test)]
mod panic_test {
    use super::*;
    use crate::CResult;

    #[test]
    #[should_panic(expected = r#"Hello World!"#)]
    fn test_panic_catcher_set_panic_hook_can_still_panic() {
        wirefilter_set_panic_catcher_hook();
        panic!("Hello World!");
    }

    #[test]
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
