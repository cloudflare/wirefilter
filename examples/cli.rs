extern crate wirefilter;

use wirefilter::Context;
use wirefilter::types::Type;

use std::cmp::max;
use std::env::args;

fn main() {
    let filter = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let context: Context<_, _> = [
        ("ip", Type::Ip),
        ("str", Type::Bytes),
        ("bytes", Type::Bytes),
        ("unsigned", Type::Unsigned),
    ].iter()
        .cloned()
        .collect();

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
