use {ErrorKind, Lex, LexResult};
use utils::{expect, span, take_while};

use cidr::{Cidr, IpCidr, NetworkParseError};
use std::net::IpAddr;
use std::str::FromStr;

impl<'a> Lex<'a> for IpAddr {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = take_while(input, "IP character", |c| match c {
            '0'...'9' | 'a'...'f' | 'A'...'F' | ':' | '.' => true,
            _ => false,
        })?;
        match IpAddr::from_str(chunk) {
            Ok(ip_addr) => Ok((ip_addr, rest)),
            Err(err) => Err((
                ErrorKind::ParseIp(NetworkParseError::AddrParseError(err)),
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
            let len = u8::from_str(digits).map_err(|e| (ErrorKind::ParseInt(e, 10), digits))?;
            (
                IpCidr::new(addr, len).map_err(|e| (ErrorKind::ParseIp(e), span(input, rest)))?,
                rest
            )
        } else {
            (IpCidr::new_host(addr), rest)
        })
    }
}
