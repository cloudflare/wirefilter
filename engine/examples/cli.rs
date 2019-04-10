extern crate wirefilter;

use std::env::args;
use wirefilter::{Function, FunctionArgKind, LhsValue, Scheme, Type};

fn panic_function<'a>(_: &[LhsValue<'a>]) -> LhsValue<'a> {
    panic!();
}

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let mut scheme = Scheme! {
        ip: Ip,
        str: Bytes,
        int: Int,
        bool: Bool,
    };

    scheme
        .add_function(
            "panic".into(),
            Function::new(Type::Bytes, panic_function)
                .param(FunctionArgKind::Field, Type::Bytes)
                .opt_param(FunctionArgKind::Literal, "".into()),
        )
        .unwrap();

    match scheme.parse(&filter) {
        Ok(res) => println!("{:#?}", res),
        Err(err) => println!("{}", err),
    }
}
