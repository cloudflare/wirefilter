use cidr::{Cidr, NetworkParseError};
use lex::{expect, span, take_while, Lex, LexErrorKind, LexResult};

use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::net::IpAddr;
use std::ops::Deref;
use std::str::FromStr;

#[derive(Serialize, Deserialize)]
pub struct IpCidr(::cidr::IpCidr);

impl Debug for IpCidr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

impl Deref for IpCidr {
    type Target = ::cidr::IpCidr;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn cmp_addr_network<C: Cidr>(addr: &C::Address, network: &C) -> Ordering
where
    C::Address: Ord,
{
    if addr > &network.last_address() {
        Ordering::Greater
    } else if addr < &network.first_address() {
        Ordering::Less
    } else {
        Ordering::Equal
    }
}

impl PartialOrd<IpCidr> for IpAddr {
    fn partial_cmp(&self, network: &IpCidr) -> Option<Ordering> {
        match (self, network) {
            (&IpAddr::V4(ref addr), &IpCidr(::cidr::IpCidr::V4(ref network))) => {
                Some(cmp_addr_network(addr, network))
            }
            (&IpAddr::V6(ref addr), &IpCidr(::cidr::IpCidr::V6(ref network))) => {
                Some(cmp_addr_network(addr, network))
            }
            _ => None,
        }
    }
}

impl PartialEq<IpCidr> for IpAddr {
    fn eq(&self, network: &IpCidr) -> bool {
        network.contains(self)
    }
}

impl<'i> Lex<'i> for IpAddr {
    fn lex(input: &str) -> LexResult<Self> {
        let (chunk, rest) = take_while(input, "IP address character", |c| match c {
            '0'...'9' | 'a'...'f' | 'A'...'F' | ':' | '.' => true,
            _ => false,
        })?;
        match Self::from_str(chunk) {
            Ok(ip_addr) => Ok((ip_addr, rest)),
            Err(err) => Err((
                LexErrorKind::ParseNetwork(NetworkParseError::AddrParseError(err)),
                chunk,
            )),
        }
    }
}

impl<'i> Lex<'i> for ::cidr::IpCidr {
    fn lex(input: &str) -> LexResult<Self> {
        // We're not using IpCidr::from_str here since it supports short IPv4
        // form which we don't want as it conflicts with singular numbers.
        let (addr, rest) = IpAddr::lex(input)?;

        Ok(if let Ok(rest) = expect(rest, "/") {
            let (digits, rest) = take_while(rest, "digit", |c| c.is_digit(10))?;
            let len = u8::from_str(digits)
                .map_err(|err| (LexErrorKind::ParseInt { err, radix: 10 }, digits))?;
            (
                Self::new(addr, len)
                    .map_err(|err| (LexErrorKind::ParseNetwork(err), span(input, rest)))?,
                rest,
            )
        } else {
            (Self::new_host(addr), rest)
        })
    }
}

impl<'i> Lex<'i> for IpCidr {
    fn lex(input: &str) -> LexResult<Self> {
        let (value, input) = ::cidr::IpCidr::lex(input)?;
        Ok((IpCidr(value), input))
    }
}
