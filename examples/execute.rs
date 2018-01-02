extern crate wirefilter;

use wirefilter::{ErrorKind, Lex};
use wirefilter::context::execution::{ExecutionContext, LhsValue};

fn main() {
    let mut args = ::std::env::args().skip(1);

    let filter = args.next()
        .expect("Expected a filter definition as a command-line argument");

    let context = ExecutionContext::new(args.map(|arg| {
        let (k, v) = arg.split_at(arg.find('=').unwrap_or_else(|| {
            panic!("Could not find = in {:?}", arg);
        }));

        let lhs_value = LhsValue::lex(&v[1..])
            .and_then(|(v, rest)| {
                if rest.is_empty() {
                    Ok(v)
                } else {
                    Err((ErrorKind::EOF, rest))
                }
            })
            .expect("Could not parse value");

        (k.to_owned(), lhs_value)
    }).collect());

    match wirefilter::filter(&filter, &context) {
        Ok(res) => println!("{:?}", res),
        Err((err, input)) => panic!("{} in {:?}", err, input),
    }
}
