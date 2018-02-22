#![feature(test)]

extern crate test;
extern crate wirefilter;

use test::{black_box, Bencher};
use wirefilter::{Context, Filter};
use wirefilter::types::Type;

#[bench]
fn parsing(b: &mut Bencher) {
    let context: Context<_, _> = [
        ("unsigned", Type::Unsigned),
        ("str", Type::Bytes),
        ("ip.src", Type::Ip),
    ].iter()
        .cloned()
        .collect();

    b.iter(|| {
        black_box(&context).parse(black_box(
            r#"ip.src != 208.130.28.0/22 || unsigned == 10 && str contains "xyz" || str ~ "\d+""#,
        ))
    });
}
