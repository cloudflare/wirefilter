use {ErrorKind, Lex, LexResult};
use std::net::{Ipv4Addr, Ipv6Addr};
use utils::{expect, span, take_while};

use cidr::{Cidr, Ipv4Cidr, Ipv6Cidr, NetworkParseError};
use std::str::FromStr;

impl<'a> Lex<'a> for Ipv4Addr {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = take_while(input, "IPv4 character", |c| match c {
            '0'...'9' | '.' => true,
            _ => false,
        })?;
        match Self::from_str(chunk) {
            Ok(ip_addr) => Ok((ip_addr, rest)),
            Err(err) => Err((
                ErrorKind::ParseIp(NetworkParseError::AddrParseError(err)),
                chunk,
            )),
        }
    }
}

impl<'a> Lex<'a> for Ipv6Addr {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = take_while(input, "IPv6 character", |c| match c {
            '0'...'9' | 'a'...'f' | 'A'...'F' | ':' | '.' => true,
            _ => false,
        })?;
        match Self::from_str(chunk) {
            Ok(ip_addr) => Ok((ip_addr, rest)),
            Err(err) => Err((
                ErrorKind::ParseIp(NetworkParseError::AddrParseError(err)),
                chunk,
            )),
        }
    }
}

fn lex_cidr<'a, C: Cidr>(input: &'a str) -> LexResult<'a, C>
where
    C::Address: Lex<'a>,
{
    // We're not using IpCidr::from_str here since it supports short IPv4
    // form which we don't want as it conflicts with singular numbers.
    let (addr, rest) = C::Address::lex(input)?;

    Ok(if let Ok(rest) = expect(rest, "/") {
        let (digits, rest) = take_while(rest, "digit", |c| c.is_digit(10))?;
        let len = u8::from_str(digits).map_err(|e| (ErrorKind::ParseInt(e, 10), digits))?;
        (
            C::new(addr, len).map_err(|e| (ErrorKind::ParseIp(e), span(input, rest)))?,
            rest,
        )
    } else {
        (C::new_host(addr), rest)
    })
}

impl<'a> Lex<'a> for Ipv4Cidr {
    fn lex(input: &str) -> LexResult<Self> {
        lex_cidr(input)
    }
}

impl<'a> Lex<'a> for Ipv6Cidr {
    fn lex(input: &str) -> LexResult<Self> {
        lex_cidr(input)
    }
}
