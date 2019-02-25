extern crate wirefilter;

use std::env::args;
use wirefilter::Scheme;

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let scheme = Scheme! {
        ip: Ip,
        str: Bytes,
        int: Int,
        bool: Bool,
    };

    match scheme.parse(&filter) {
        Ok(res) => println!("{:#?}", res),
        Err(err) => println!("{}", err),
    }
}
