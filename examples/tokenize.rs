extern crate wirefilter;

use wirefilter::context::ast::AstContext;

fn main() {
    let filter = ::std::env::args()
        .nth(1)
        .expect("Expected an input as a command-line argument");

    let context = AstContext::new(&filter);

    match wirefilter::filter(&filter, context) {
        Ok(res) => println!("{:#?}", res),
        Err((err, input)) => panic!("{} in {:?}", err, input),
    }
}
