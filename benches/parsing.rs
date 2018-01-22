#![feature(test)]

extern crate bincode;
extern crate serde;
extern crate serde_cbor;
extern crate serde_json;
extern crate test;
extern crate wirefilter;

use wirefilter::{Context, Filter};
use wirefilter::types::Type;
use test::{black_box, Bencher};
use serde::Serialize;

fn print_serialized(serialized: &[u8]) {
    print!("`");

    for b in serialized.iter().cloned() {
        if b == b'`' || b == b'\\' {
            print!("\\");
        }
        match b {
            0x00 => print!("\\0"),
            0x20...0x7E => print!("{}", b as char),
            _ => print!("\\x{:02X}", b),
        }
    }

    print!("` ({} bytes) ", serialized.len());
}

fn get_default_source() -> &'static str {
    black_box(r#"ip.src != 208.130.28.0/22 || unsigned == 10 && str contains "xyz" || str ~ "\d+""#)
}

fn create_default_context() -> Context<&'static str, Type> {
    black_box([
        ("unsigned", Type::Unsigned),
        ("str", Type::Bytes),
        ("ip.src", Type::Ip),
    ]).iter()
        .cloned()
        .collect()
}

fn parse_sample_filter<'a>(context: &'a Context<&'static str, Type>) -> Filter<'a> {
    context.parse(get_default_source()).unwrap()
}

macro_rules! serde_bench {
    ($target:ident { $ser:path, $de:path }) => {
        mod $target {
            use super::*;

            #[bench]
            fn a_serializer(b: &mut Bencher) {
                let context = create_default_context();
                let filter = parse_sample_filter(&context);

                b.iter(|| {
                    black_box($ser(black_box(&filter)).unwrap())
                });

                print_serialized(&$ser(&filter).unwrap());
            }

            #[bench]
            fn b_deserializer(b: &mut Bencher) {
                let serialized: Vec<u8> = $ser(
                    &parse_sample_filter(&create_default_context())
                ).unwrap();

                b.iter(|| {
                    let filter: Filter = $de(black_box(&serialized)).unwrap();
                    black_box(filter)
                });
            }
        }
    };
}

#[bench]
fn filter_parser(b: &mut Bencher) {
    let context = create_default_context();

    b.iter(|| black_box(parse_sample_filter(&context)));

    print_serialized(get_default_source().as_bytes());
}

serde_bench!(bench_json {
    serde_json::to_vec,
    serde_json::from_slice
});

serde_bench!(bench_cbor {
    serde_cbor::to_vec,
    serde_cbor::from_slice
});

fn serialize_bincode<T: Serialize>(value: &T) -> bincode::Result<Vec<u8>> {
    bincode::serialize(value, bincode::Infinite)
}

serde_bench!(bench_bincode {
    serialize_bincode,
    bincode::deserialize
});
