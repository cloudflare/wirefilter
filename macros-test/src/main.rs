
use wirefilter_macros::*;
use wirefilter::filterable::*;
use wirefilter::*;
use std::net::IpAddr;

#[derive(Debug, Filterable)]
struct Empty{
    a: String,
    b: IpAddr,
    c: usize,
}

fn main() {
    let scheme = Scheme!(
        a: Bytes,
        b: Ip,
        c: Int
    );
    let e = Empty{
        a: String::from("A"),
        b: IpAddr::from([1,1,1,1]),
        c: 1234
    };
    e.filter_context(&scheme).unwrap();
    println!("Hello, world!");
}
