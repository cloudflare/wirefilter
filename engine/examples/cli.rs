extern crate wirefilter;

use std::env::args;
use wirefilter::{Scheme, Type};

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let scheme: Scheme = (&[
        ("ip", Type::Ip),
        ("str", Type::Bytes),
        ("bytes", Type::Bytes),
        ("int", Type::Int),
        ("bool", Type::Bool),
    ])
        .into();

    match scheme.parse(&filter) {
        Ok(res) => println!("{:#?}", res),
        Err(err) => println!("{}", err),
    }
}
