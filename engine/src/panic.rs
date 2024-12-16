use backtrace::Backtrace;
use std::cell::{Cell, RefCell};
use std::io::{self, Write};
use std::panic::UnwindSafe;
use std::process::abort;
use std::sync::atomic::{AtomicBool, Ordering};

/// Describes the fallback behavior when
/// a panic occurs outside of `catch_panic`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PanicCatcherFallbackMode {
    /// Continue running the subsequent panic hooks.
    Continue,
    /// Abort the program immediatly.
    Abort,
}

thread_local! {
    // String to store last backtrace that is recorded in the panic catcher hook
    static PANIC_CATCHER_BACKTRACE : RefCell<String> = const { RefCell::new(String::new()) };

    // Integer to track the number of nested `catch_panic` calls.
    static PANIC_CATCHER_LEVEL: Cell<u64> = const { Cell::new(0) };

    // Fallback mode for when the hook is set but a panic occurs outside of a catch block
    static PANIC_CATCHER_FALLBACK_MODE: Cell<PanicCatcherFallbackMode> = const { Cell::new(PanicCatcherFallbackMode::Continue) };

    // Status of the panic catcher
    static PANIC_CATCHER_ENABLED: Cell<bool> = const { Cell::new(false) };
}
static PANIC_CATCHER_HOOK_SET: AtomicBool = AtomicBool::new(false);

#[inline]
fn panic_catcher_start_catching() -> bool {
    if PANIC_CATCHER_ENABLED.with(|b| b.get()) {
        PANIC_CATCHER_LEVEL.with(|b| {
            let Some(level) = b.get().checked_add(1) else {
                abort()
            };
            b.set(level)
        });
        true
    } else {
        false
    }
}

#[inline]
fn panic_catcher_stop_catching() {
    PANIC_CATCHER_LEVEL.with(|b| {
        let Some(level) = b.get().checked_sub(1) else {
            abort()
        };
        b.set(level)
    });
}

/// Retrieves the backtrace stored during the last panic
/// for the current thread.
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

/// Configures the fallback behavior when
/// a panic occurs outside of `catch_panic`.
pub fn panic_catcher_set_fallback_mode(
    fallback_mode: PanicCatcherFallbackMode,
) -> PanicCatcherFallbackMode {
    PANIC_CATCHER_FALLBACK_MODE.with(|b| b.replace(fallback_mode))
}

/// Catch a panic.
#[inline(always)]
pub fn catch_panic<F, T>(f: F) -> Result<T, String>
where
    F: FnOnce() -> T + UnwindSafe,
{
    if panic_catcher_start_catching() {
        let result = std::panic::catch_unwind(f);
        panic_catcher_stop_catching();
        match result {
            Ok(res) => Ok(res),
            Err(_) => Err(panic_catcher_get_backtrace().unwrap_or_else(|| {
                "thread '<unknown>' panicked at '<unknown>' in file '<unknown>' at line 0"
                    .to_string()
            })),
        }
    } else {
        Ok(f())
    }
}

fn record_backtrace(info: &std::panic::PanicHookInfo<'_>, bt: &mut String) {
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
            Backtrace::new()
        ),
    );
}

/// Registers panic catcher panic hook.
pub fn panic_catcher_set_hook() {
    if PANIC_CATCHER_HOOK_SET.load(Ordering::SeqCst) {
        return;
    }
    let next = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if PANIC_CATCHER_LEVEL.with(|enabled| enabled.get() > 0) {
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
                abort();
            }
        }
    }));
    PANIC_CATCHER_HOOK_SET.store(true, Ordering::SeqCst);
}

/// Enables the panic catcher.
pub fn panic_catcher_enable() {
    PANIC_CATCHER_ENABLED.with(|b| b.set(true));
}

/// Disables the panic catcher.
pub fn panic_catcher_disable() {
    PANIC_CATCHER_ENABLED.with(|b| b.set(false));
}

#[cfg(test)]
mod panic_test {
    use super::*;

    #[test]
    #[cfg_attr(miri, ignore)]
    #[should_panic(expected = r#"Hello World!"#)]
    fn test_panic_catcher_set_panic_hook_can_still_panic() {
        panic_catcher_set_hook();
        panic!("Hello World!");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[should_panic(expected = r#"Hello World!"#)]
    fn test_panic_catcher_enabled_disabled_can_still_panic() {
        panic_catcher_set_hook();
        panic_catcher_enable();
        panic_catcher_disable();
        panic!("Hello World!");
    }

    #[test]
    fn test_panic_catcher_can_catch_panic() {
        panic_catcher_set_hook();
        assert_eq!(
            panic_catcher_set_fallback_mode(PanicCatcherFallbackMode::Abort),
            PanicCatcherFallbackMode::Continue
        );
        panic_catcher_enable();
        match catch_panic::<_, ()>(|| panic!("Halt and Catch Panic")) {
            Ok(_) => unreachable!(),
            Err(msg) => assert!(msg.contains("Halt and Catch Panic")),
        }
        panic_catcher_disable();
    }

    #[test]
    fn test_panic_catcher_can_catch_panic_nested() {
        panic_catcher_set_hook();
        assert_eq!(
            panic_catcher_set_fallback_mode(PanicCatcherFallbackMode::Abort),
            PanicCatcherFallbackMode::Continue
        );
        panic_catcher_enable();
        match catch_panic::<_, ()>(|| {
            catch_panic::<_, ()>(|| panic!("Nested Panic is Caught")).unwrap_err();
            panic!("Halt and Catch Panic")
        }) {
            Ok(_) => unreachable!(),
            Err(msg) => assert!(msg.contains("Halt and Catch Panic")),
        }
        panic_catcher_disable();
    }
}
