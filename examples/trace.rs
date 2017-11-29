extern crate wirefilter;

use std::env::args;
use wirefilter::{Parse, Filter};

fn main() {
    let s = args().nth(1).expect("Expected a filter as a command-line argument");
    println!("{:#?}", Filter::parse(&s));
}
