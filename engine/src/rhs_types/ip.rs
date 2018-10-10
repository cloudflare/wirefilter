use cidr::{Cidr, IpCidr, Ipv4Cidr, Ipv6Cidr, NetworkParseError};
use lex::{take_while, Lex, LexError, LexErrorKind, LexResult};
use std::{
    cmp::Ordering,
    net::{IpAddr, Ipv4Addr, Ipv6Addr},
    ops::RangeInclusive,
    str::FromStr,
};
use strict_partial_ord::StrictPartialOrd;

fn match_addr_or_cidr(input: &str) -> LexResult<&str> {
    take_while(input, "IP address character", |c| match c {
        '0'...'9' | 'a'...'f' | 'A'...'F' | ':' | '.' | '/' => true,
        _ => false,
    })
}

fn parse_addr(input: &str) -> Result<IpAddr, LexError> {
    IpAddr::from_str(input).map_err(|err| {
        (
            LexErrorKind::ParseNetwork(NetworkParseError::AddrParseError(err)),
            input,
        )
    })
}

impl<'i> Lex<'i> for IpAddr {
    fn lex(input: &str) -> LexResult<Self> {
        let (input, rest) = match_addr_or_cidr(input)?;
        parse_addr(input).map(|res| (res, rest))
    }
}

#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
#[serde(untagged)]
pub enum ExplicitIpRange {
    V4(RangeInclusive<Ipv4Addr>),
    V6(RangeInclusive<Ipv6Addr>),
}

#[derive(PartialEq, Eq, Clone, Serialize, Debug)]
#[serde(untagged)]
pub enum IpRange {
    Explicit(ExplicitIpRange),
    Cidr(IpCidr),
}

impl<'i> Lex<'i> for IpRange {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = match_addr_or_cidr(input)?;

        // check for ".." before trying to lex an address
        let range = if let Some(split_pos) = chunk.find("..") {
            let first = parse_addr(&chunk[..split_pos])?;
            let last = parse_addr(&chunk[split_pos + "..".len()..])?;

            IpRange::Explicit(match (first, last) {
                (IpAddr::V4(first), IpAddr::V4(last)) if first <= last => {
                    ExplicitIpRange::V4(first..=last)
                }
                (IpAddr::V6(first), IpAddr::V6(last)) if first <= last => {
                    ExplicitIpRange::V6(first..=last)
                }
                _ => {
                    return Err((LexErrorKind::IncompatibleRangeBounds, chunk));
                }
            })
        } else {
            IpRange::Cidr(::cidr::IpCidr::from_str(chunk).map_err(|err| {
                let split_pos = chunk.find('/').unwrap_or_else(|| chunk.len());
                let err_span = match err {
                    NetworkParseError::AddrParseError(_) | NetworkParseError::InvalidHostPart => {
                        &chunk[..split_pos]
                    }
                    NetworkParseError::NetworkLengthParseError(_) => &chunk[split_pos + 1..],
                    NetworkParseError::NetworkLengthTooLongError(_) => chunk,
                };
                (LexErrorKind::ParseNetwork(err), err_span)
            })?)
        };

        Ok((range, rest))
    }
}

macro_rules! impl_ip_range_from {
    (@single $v:ident, |$input:ident: $ty:ty| $transform:expr) => {
        impl From<$ty> for ExplicitIpRange {
            fn from($input: $ty) -> Self {
                ExplicitIpRange::$v($transform)
            }
        }
    };

    ($ty:ident { $v4:ty, $v6:ty }, |$input:ident| $transform:expr) => {
        impl_ip_range_from!(@single V4, |$input: $v4| $transform);
        impl_ip_range_from!(@single V6, |$input: $v6| $transform);

        impl From<$ty> for ExplicitIpRange {
            fn from($input: $ty) -> Self {
                match $input {
                    $ty::V4($input) => $input.into(),
                    $ty::V6($input) => $input.into(),
                }
            }
        }
    };
}

impl_ip_range_from!(IpAddr { Ipv4Addr, Ipv6Addr }, |addr| addr..=addr);
impl_ip_range_from!(IpCidr { Ipv4Cidr, Ipv6Cidr }, |cidr| cidr.first_address()
    ..=cidr.last_address());

impl From<IpRange> for ExplicitIpRange {
    fn from(range: IpRange) -> Self {
        match range {
            IpRange::Explicit(range) => range,
            IpRange::Cidr(cidr) => cidr.into(),
        }
    }
}

impl StrictPartialOrd for IpAddr {
    fn strict_partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (IpAddr::V4(lhs), IpAddr::V4(rhs)) => Some(lhs.cmp(rhs)),
            (IpAddr::V6(lhs), IpAddr::V6(rhs)) => Some(lhs.cmp(rhs)),
            _ => None,
        }
    }
}

#[test]
fn test_lex() {
    fn addr<A: Into<IpAddr>>(addr: A) -> IpRange {
        IpRange::Cidr(IpCidr::new_host(addr.into()))
    }

    fn range<A: Into<IpAddr>>(range: RangeInclusive<A>) -> IpRange {
        let (first, last) = range.into_inner();
        match (first.into(), last.into()) {
            (IpAddr::V4(first), IpAddr::V4(last)) => {
                IpRange::Explicit(ExplicitIpRange::V4(first..=last))
            }
            (IpAddr::V6(first), IpAddr::V6(last)) => {
                IpRange::Explicit(ExplicitIpRange::V6(first..=last))
            }
            _ => panic!("Invalid inputs"),
        }
    }

    fn cidr<A: Into<IpAddr>>(addr: A, len: u8) -> IpRange {
        IpRange::Cidr(IpCidr::new(addr.into(), len).unwrap())
    }

    assert_ok!(IpRange::lex("12.34.56.78;"), addr([12, 34, 56, 78]), ";");
    assert_ok!(
        IpRange::lex("12.34.56.0/24;"),
        cidr([12, 34, 56, 0], 24),
        ";"
    );
    assert_ok!(
        IpRange::lex("12.34.56.0/32;"),
        cidr([12, 34, 56, 0], 32),
        ";"
    );
    assert_ok!(IpRange::lex("::/10;"), cidr([0; 16], 10), ";");
    assert_ok!(
        IpRange::lex("::ffff:12.34.56.78/127;"),
        cidr(
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 12, 34, 56, 78],
            127
        ),
        ";"
    );
    assert_ok!(
        IpRange::lex("1234::5678"),
        addr([0x1234, 0, 0, 0, 0, 0, 0, 0x5678])
    );
    assert_ok!(
        IpRange::lex("10.0.0.0..127.0.0.1 "),
        range([10, 0, 0, 0]..=[127, 0, 0, 1]),
        " "
    );
    assert_ok!(
        IpRange::lex("::1..::2||"),
        range([0, 0, 0, 0, 0, 0, 0, 1]..=[0, 0, 0, 0, 0, 0, 0, 2]),
        "||"
    );
    match IpRange::lex("10.0.0.0/100") {
        Err((
            LexErrorKind::ParseNetwork(NetworkParseError::NetworkLengthTooLongError(_)),
            "10.0.0.0/100",
        )) => {}
        err => panic!("Expected NetworkLengthTooLongError, got {:?}", err),
    }
    assert_err!(
        IpRange::lex("::/.1"),
        LexErrorKind::ParseNetwork(NetworkParseError::NetworkLengthParseError(
            u8::from_str(".1").unwrap_err()
        )),
        ".1"
    );
    assert_err!(
        IpRange::lex("10.0.0.0..::1"),
        LexErrorKind::IncompatibleRangeBounds,
        "10.0.0.0..::1"
    );
    assert_err!(
        IpRange::lex("::1..10.0.0.0"),
        LexErrorKind::IncompatibleRangeBounds,
        "::1..10.0.0.0"
    );
    assert_err!(
        IpRange::lex("127.0.0.1..10.0.0.0"),
        LexErrorKind::IncompatibleRangeBounds,
        "127.0.0.1..10.0.0.0"
    );
    assert_err!(
        IpRange::lex("::2..::1"),
        LexErrorKind::IncompatibleRangeBounds,
        "::2..::1"
    );
    assert_err!(
        IpRange::lex("10.0.0.0.0/10"),
        LexErrorKind::ParseNetwork(NetworkParseError::AddrParseError(
            IpAddr::from_str("10.0.0.0.0").unwrap_err()
        )),
        "10.0.0.0.0"
    );
}

#[test]
fn test_strict_partial_ord() {
    let ips = &[
        IpAddr::from([10, 0, 0, 0]),
        IpAddr::from([127, 0, 0, 1]),
        IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1]),
        IpAddr::from([0, 0, 0, 0, 0, 0, 0, 2]),
    ];

    for lhs in ips {
        for rhs in ips {
            if lhs.is_ipv4() == rhs.is_ipv4() {
                assert_eq!(lhs.strict_partial_cmp(rhs), lhs.partial_cmp(rhs));
            } else {
                assert_eq!(lhs.strict_partial_cmp(rhs), None);
            }
        }
    }
}
