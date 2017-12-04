extern crate wirefilter;

use std::env::args;
use wirefilter::tokenizer::{Lex, Token};

fn main() {
    let s = args()
        .nth(1)
        .expect("Expected an input as a command-line argument");
    let mut input = s.as_str();
    while !input.is_empty() {
        match Token::lex(input) {
            Ok((token, rest)) => {
                println!("Token: {:?}", token);
                input = rest;
            }
            Err((err, rest)) => {
                eprintln!("`{}`", s);
                let offset = (rest.as_ptr() as usize) - (s.as_ptr() as usize);
                for _ in 0..(offset + 1) {
                    eprint!(" ");
                }
                for _ in 0..::std::cmp::max(rest.len(), 1) {
                    eprint!("^");
                }
                eprintln!(" {}", err);
                ::std::process::exit(1);
            }
        };
    }
}
