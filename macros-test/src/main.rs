
use wirefilter_macros::*;
use wirefilter::filterable::*;
use wirefilter::*;

#[derive(Debug, Filterable)]
struct Empty;




fn main() {
    let scheme = Scheme!(
        blah: Bytes
    );
    let e = Empty{};
    e.filter_context(&scheme).unwrap();
    println!("Hello, world!");
}
