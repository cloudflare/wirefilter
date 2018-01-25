use cidr::{Cidr, NetworkParseError};
use lex::{expect, span, take_while, Lex, LexErrorKind, LexResult};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde::de::Error;

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt::{self, Debug, Formatter};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::ops::Deref;
use std::str::FromStr;

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

#[derive(Serialize, Deserialize)]
struct IpCidrRepr<'i> {
    #[serde(borrow)]
    #[serde(with = "::serde_bytes")]
    address: Cow<'i, [u8]>,

    network_length: u8,
}

impl Serialize for IpCidr {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        // if ser.is_human_readable() {
        //     return self.to_string().serialize(ser);
        // }
        match self.0 {
            ::cidr::IpCidr::V4(ref cidr) => IpCidrRepr {
                address: Cow::Borrowed(&cidr.first_address().octets()),
                network_length: cidr.network_length(),
            }.serialize(ser),
            ::cidr::IpCidr::V6(ref cidr) => IpCidrRepr {
                address: Cow::Borrowed(&cidr.first_address().octets()),
                network_length: cidr.network_length(),
            }.serialize(ser),
        }
    }
}

impl<'de> Deserialize<'de> for IpCidr {
    fn deserialize<D: Deserializer<'de>>(de: D) -> Result<Self, D::Error> {
        // if de.is_human_readable() {
        //     let s: &str = Deserialize::deserialize(de)?;
        //     return match s.parse() {
        //         Ok(cidr) => Ok(IpCidr(cidr)),
        //         Err(err) => Err(D::Error::custom(err)),
        //     };
        // }
        let repr = IpCidrRepr::deserialize(de)?;
        let addr = match repr.address.len() {
            4 => IpAddr::V4(Ipv4Addr::from(unsafe {
                *(repr.address.as_ptr() as *const [u8; 4])
            })),
            16 => IpAddr::V6(Ipv6Addr::from(unsafe {
                *(repr.address.as_ptr() as *const [u8; 16])
            })),
            _ => {
                return Err(D::Error::invalid_length(
                    repr.address.len(),
                    &"4 for IPv4 or 16 for IPv16",
                ))
            }
        };
        match ::cidr::IpCidr::new(addr, repr.network_length) {
            Ok(cidr) => Ok(IpCidr(cidr)),
            Err(err) => Err(D::Error::custom(err)),
        }
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
