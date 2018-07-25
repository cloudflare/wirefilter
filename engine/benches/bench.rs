#![feature(test)]

extern crate test;
extern crate wirefilter;

use std::net::IpAddr;
use test::{black_box, Bencher};
use wirefilter::{ExecutionContext, Filter, Scheme, Type};

fn create_scheme() -> Scheme {
    [
        ("http.cookie", Type::Bytes),
        ("http.host", Type::Bytes),
        ("http.request.uri.path", Type::Bytes),
        ("http.user_agent", Type::Bytes),
        ("ip.addr", Type::Ip),
        ("ip.geoip.asnum", Type::Bytes),
        ("ip.geoip.country", Type::Bytes),
        ("ssl", Type::Bool),
        ("tcp.port", Type::Unsigned),
    ].iter()
        .map(|&(k, t)| (k.to_owned(), t))
        .collect()
}

fn create_exec_contexts(scheme: &Scheme) -> Vec<ExecutionContext> {
    vec![
        {
            let mut ctx = ExecutionContext::new(scheme);
            ctx.set_field_value("http.cookie", "test=321;access_token=123");
            ctx.set_field_value("http.host", "www.lfgss.com");
            ctx.set_field_value("http.request.uri.path", "/static/imgs/1.jpeg");
            ctx.set_field_value(
                "http.user_agent",
                "Mozilla/5.0 (compatible; YandexBot/3.0; +http://yandex.com/bots)",
            );
            ctx.set_field_value("ip.addr", IpAddr::from([212, 71, 253, 211]));
            ctx.set_field_value("ip.geoip.asnum", "AS30992");
            ctx.set_field_value("ip.geoip.country", "VN");
            ctx.set_field_value("ssl", true);
            ctx.set_field_value("tcp.port", 443);
            ctx
        },
        {
            let mut ctx = ExecutionContext::new(scheme);
            ctx.set_field_value("http.cookie", "foo=bar");
            ctx.set_field_value("http.host", "static.lfgss.com");
            ctx.set_field_value(
                "http.user_agent",
                "Mozilla/5.0 (compatible; SomeBot/3.0; +http://yandex.com/bots)",
            );
            ctx.set_field_value("ip.addr", IpAddr::from([176, 58, 105, 63]));
            ctx.set_field_value("ip.geoip.asnum", "AS30993");
            ctx.set_field_value("ip.geoip.country", "JP");
            ctx.set_field_value("ssl", false);
            ctx.set_field_value("tcp.port", 80);
            ctx
        },
    ]
}

fn parse_filters<'s>(scheme: &'s Scheme) -> Vec<Filter<'s>> {
    include_str!("filters.dat")
        .split_terminator("\n")
        .map(|src| scheme.parse(src).unwrap())
        .collect()
}

#[bench]
fn parsing(b: &mut Bencher) {
    let scheme = create_scheme();

    b.iter(|| {
        black_box(parse_filters(&scheme));
    });
}

#[bench]
fn matching(b: &mut Bencher) {
    let scheme = create_scheme();
    let filters = parse_filters(&scheme);
    let exec_contexts = create_exec_contexts(&scheme);

    b.iter(|| {
        for exec_ctx in exec_contexts.iter() {
            for filter in filters.iter() {
                black_box(filter.execute(exec_ctx));
            }
        }
    });
}
