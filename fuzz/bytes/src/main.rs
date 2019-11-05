#[macro_use]
extern crate afl;
extern crate wirefilter;

use wirefilter::{ExecutionContext, Scheme, Type};

fn main() {
    fuzz!(|data: &[u8]| {
        let scheme = Scheme! { foo: Bytes };
        let filter = scheme.parse("foo == \"\"").unwrap().compile();
        let mut ctx = ExecutionContext::new(&scheme);
        ctx.set_field_value("foo", data).unwrap();

        filter.execute(&ctx).unwrap();
    });
}
