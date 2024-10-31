// This is up here to make the Scheme macro happy
#[cfg(fuzzing)]
use wirefilter::{ExecutionContext, Scheme};

#[cfg(fuzzing)]
fn main() {
    fuzz!(|data: &[u8]| {
        let scheme = Scheme! { foo: Bytes };
        let filter = scheme.parse("foo == \"\"").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value(scheme.get_field("foo").unwrap(), data)
            .unwrap();

        filter.execute(&ctx).unwrap();
    });
}

#[cfg(not(fuzzing))]
fn main() {
    panic!("must compile with `cargo afl build`, not `cargo build`")
}
