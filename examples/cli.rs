extern crate wirefilter;

use wirefilter::filter::{ParsingContext, Type};
use std::iter::FromIterator;
use std::cmp::max;

fn main() {
    let filter = ::std::env::args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let context = ParsingContext::from_iter(vec![("ip.v4", Type::IpAddrV4)]);

    match context.parse(&filter) {
        Ok(res) => println!("{:#?}", res),
        Err((err, span)) => {
            println!("`{}`", filter);
            for _ in 0..1 + span.as_ptr() as usize - filter.as_ptr() as usize {
                print!(" ");
            }
            for _ in 0..max(1, span.len()) {
                print!("^");
            }
            println!(" {}", err);
        }
    }
}
