use tokenizer::{ErrorKind, Lex, LexResult};
use tokenizer::utils::take_while;

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
            Err(err) => Err((ErrorKind::ParseIpAddr(err), chunk)),
        }
    }
}
