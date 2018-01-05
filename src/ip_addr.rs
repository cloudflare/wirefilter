use cidr::{Cidr, IpCidr, NetworkParseError};
use lex::{expect, span, take_while, Lex, LexErrorKind, LexResult};

use std::net::IpAddr;
use std::str::FromStr;

impl<'a> Lex<'a> for IpAddr {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = take_while(input, "IP address character", |c| match c {
            '0'...'9' | 'a'...'f' | 'A'...'F' | ':' | '.' => true,
            _ => false,
        })?;
        match Self::from_str(chunk) {
            Ok(ip_addr) => Ok((ip_addr, rest)),
            Err(err) => Err((
                LexErrorKind::ParseIp(NetworkParseError::AddrParseError(err)),
                chunk,
            )),
        }
    }
}

impl<'a> Lex<'a> for IpCidr {
    fn lex(input: &str) -> LexResult<Self> {
        // We're not using IpCidr::from_str here since it supports short IPv4
        // form which we don't want as it conflicts with singular numbers.
        let (addr, rest) = IpAddr::lex(input)?;

        Ok(if let Ok(rest) = expect(rest, "/") {
            let (digits, rest) = take_while(rest, "digit", |c| c.is_digit(10))?;
            let len = u8::from_str(digits).map_err(|e| (LexErrorKind::ParseInt(e, 10), digits))?;
            (
                Self::new(addr, len).map_err(|e| (LexErrorKind::ParseIp(e), span(input, rest)))?,
                rest,
            )
        } else {
            (Self::new_host(addr), rest)
        })
    }
}
