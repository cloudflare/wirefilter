#![feature(test)]

extern crate test;
extern crate wirefilter;

use std::net::IpAddr;
use std::str::FromStr;
use test::{black_box, Bencher};
use wirefilter::Context;
use wirefilter::Filter;
use wirefilter::types::{LhsValue, Type};

fn create_scheme() -> Context<&'static str, Type> {
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
        .cloned()
        .collect()
}

fn create_exec_contexts() -> Vec<Context<&'static str, LhsValue<'static>>> {
    [
        [
            (
                "http.cookie",
                LhsValue::Bytes(r#"test=321;access_token=123"#.as_bytes().into()),
            ),
            (
                "http.host",
                LhsValue::Bytes(r#"www.lfgss.com"#.as_bytes().into()),
            ),
            (
                "http.request.uri.path",
                LhsValue::Bytes(r#"/static/imgs/1.jpeg"#.as_bytes().into()),
            ),
            (
                "http.user_agent",
                LhsValue::Bytes(
                    r#"Mozilla/5.0 (compatible; YandexBot/3.0; +http://yandex.com/bots)"#.as_bytes()
                        .into(),
                ),
            ),
            (
                "ip.addr",
                LhsValue::Ip(IpAddr::from_str("212.71.253.211").unwrap()),
            ),
            (
                "ip.geoip.asnum",
                LhsValue::Bytes(r#"AS30992"#.as_bytes().into()),
            ),
            (
                "ip.geoip.country",
                LhsValue::Bytes(r#"VN"#.as_bytes().into()),
            ),
            ("ssl", LhsValue::Bool(true)),
            ("tcp.port", LhsValue::Unsigned(443)),
        ],
        [
            (
                "http.cookie",
                LhsValue::Bytes(r#"foo=bar"#.as_bytes().into()),
            ),
            (
                "http.host",
                LhsValue::Bytes(r#"static.lfgss.com""#.as_bytes().into()),
            ),
            (
                "http.request.uri.path",
                LhsValue::Bytes(r#"test/isogram-123"#.as_bytes().into()),
            ),
            (
                "http.user_agent",
                LhsValue::Bytes(
                    r#"Mozilla/5.0 (compatible; SomeBot/3.0; +http://yandex.com/bots)"#.as_bytes()
                        .into(),
                ),
            ),
            (
                "ip.addr",
                LhsValue::Ip(IpAddr::from_str("176.58.105.63").unwrap()),
            ),
            (
                "ip.geoip.asnum",
                LhsValue::Bytes(r#"AS30993"#.as_bytes().into()),
            ),
            (
                "ip.geoip.country",
                LhsValue::Bytes(r#"JP"#.as_bytes().into()),
            ),
            ("ssl", LhsValue::Bool(false)),
            ("tcp.port", LhsValue::Unsigned(80)),
        ],
    ].iter()
        .map(|values| values.iter().cloned().collect())
        .collect()
}

fn parse_filters<'c>(scheme: &'c Context<&'static str, Type>) -> Vec<Filter<'c>> {
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
    let exec_contexts = create_exec_contexts();

    b.iter(|| {
        for exec_ctx in exec_contexts.iter() {
            for filter in filters.iter() {
                black_box(exec_ctx.execute(filter));
            }
        }
    });
}
