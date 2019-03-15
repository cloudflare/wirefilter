extern crate wirefilter;

use std::env::args;
use wirefilter::{Function, FunctionArg, FunctionArgKind, FunctionImpl, LhsValue, Scheme, Type};

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
            Function {
                args: vec![FunctionArg {
                    arg_kind: FunctionArgKind::Field,
                    val_type: Type::Bytes,
                }],
                opt_args: vec![],
                return_type: Type::Bytes,
                implementation: FunctionImpl::new(panic_function),
            },
        )
        .unwrap();

    match scheme.parse(&filter) {
        Ok(res) => println!("{:#?}", res),
        Err(err) => println!("{}", err),
    }
}
