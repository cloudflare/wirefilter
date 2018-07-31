use cidr::{Cidr, NetworkParseError};
use lex::{take_while, Lex, LexError, LexErrorKind, LexResult};

use std::{net::IpAddr, ops::RangeInclusive, str::FromStr};

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

impl<'i> Lex<'i> for RangeInclusive<IpAddr> {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = match_addr_or_cidr(input)?;

        // check for ".." before trying to lex an address
        let range = if let Some(split_pos) = chunk.find("..") {
            let first = parse_addr(&chunk[..split_pos])?;
            let last = parse_addr(&chunk[split_pos + "..".len()..])?;

            match (first, last) {
                (IpAddr::V4(_), IpAddr::V4(_)) | (IpAddr::V6(_), IpAddr::V6(_))
                    if first <= last => {}
                _ => {
                    return Err((LexErrorKind::IncompatibleRangeBounds, chunk));
                }
            }

            first..=last
        } else {
            let cidr = ::cidr::IpCidr::from_str(chunk).map_err(|err| {
                let split_pos = chunk.find('/').unwrap_or(chunk.len());
                let err_span = match err {
                    NetworkParseError::AddrParseError(_) | NetworkParseError::InvalidHostPart => {
                        &chunk[..split_pos]
                    }
                    NetworkParseError::NetworkLengthParseError(_) => &chunk[split_pos + 1..],
                    NetworkParseError::NetworkLengthTooLongError(_) => chunk,
                };
                (LexErrorKind::ParseNetwork(err), err_span)
            })?;

            cidr.first_address()..=cidr.last_address()
        };

        Ok((range, rest))
    }
}

#[test]
fn test() {
    use cidr::IpCidr;

    type IpAddrs = RangeInclusive<IpAddr>;

    fn cidr<A: Into<IpAddr>>(addr: A, len: u8) -> RangeInclusive<IpAddr> {
        let cidr = IpCidr::new(addr.into(), len).unwrap();
        cidr.first_address()..=cidr.last_address()
    }

    assert_ok!(
        IpAddrs::lex("12.34.56.78;"),
        cidr([12, 34, 56, 78], 32),
        ";"
    );
    assert_ok!(
        IpAddrs::lex("12.34.56.0/24;"),
        cidr([12, 34, 56, 0], 24),
        ";"
    );
    assert_ok!(IpAddrs::lex("::/10;"), cidr([0; 16], 10), ";");
    assert_ok!(
        IpAddrs::lex("::ffff:12.34.56.78/127;"),
        cidr(
            [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff, 12, 34, 56, 78],
            127
        ),
        ";"
    );
    assert_ok!(
        IpAddrs::lex("1234::5678"),
        cidr([0x1234, 0, 0, 0, 0, 0, 0, 0x5678], 128)
    );
    assert_ok!(
        IpAddrs::lex("10.0.0.0..127.0.0.1 "),
        IpAddr::from([10, 0, 0, 0])..=IpAddr::from([127, 0, 0, 1]),
        " "
    );
    assert_ok!(
        IpAddrs::lex("::1..::2||"),
        IpAddr::from([0, 0, 0, 0, 0, 0, 0, 1])..=IpAddr::from([0, 0, 0, 0, 0, 0, 0, 2]),
        "||"
    );
    match IpAddrs::lex("10.0.0.0/100") {
        Err((
            LexErrorKind::ParseNetwork(NetworkParseError::NetworkLengthTooLongError(_)),
            "10.0.0.0/100",
        )) => {}
        err => panic!("Expected NetworkLengthTooLongError, got {:?}", err),
    }
    assert_err!(
        IpAddrs::lex("::/.1"),
        LexErrorKind::ParseNetwork(NetworkParseError::NetworkLengthParseError(
            u8::from_str(".1").unwrap_err()
        )),
        ".1"
    );
    assert_err!(
        IpAddrs::lex("10.0.0.0..::1"),
        LexErrorKind::IncompatibleRangeBounds,
        "10.0.0.0..::1"
    );
    assert_err!(
        IpAddrs::lex("::1..10.0.0.0"),
        LexErrorKind::IncompatibleRangeBounds,
        "::1..10.0.0.0"
    );
    assert_err!(
        IpAddrs::lex("127.0.0.1..10.0.0.0"),
        LexErrorKind::IncompatibleRangeBounds,
        "127.0.0.1..10.0.0.0"
    );
    assert_err!(
        IpAddrs::lex("::2..::1"),
        LexErrorKind::IncompatibleRangeBounds,
        "::2..::1"
    );
    assert_err!(
        IpAddrs::lex("10.0.0.0.0/10"),
        LexErrorKind::ParseNetwork(NetworkParseError::AddrParseError(
            IpAddr::from_str("10.0.0.0.0").unwrap_err()
        )),
        "10.0.0.0.0"
    );
}
