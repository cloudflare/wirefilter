use std::{
    iter,
    net::{IpAddr, Ipv4Addr, Ipv6Addr},
};

use crate::{FunctionArgs, FunctionDefinition, LhsValue, Type};

/// `cidr` Function (Cloudflare Ruleset Engine)
///
/// This documentation describes the behavior and usage of the `cidr` function
/// within Cloudflare's Ruleset Engine. It is not a native Rust function,
/// but rather a built-in function available for use in Cloudflare rule expressions.
///
/// The `cidr` function returns the network address corresponding to a given IP address
/// (IPv4 or IPv6), based on the specified network bit length (prefix length).
/// It is instrumental in creating rules that match traffic based on network segments
/// rather than individual IP addresses.
///
/// # Syntax in Ruleset Engine Expressions
///
/// `cidr(address, ipv4_network_bits, ipv6_network_bits)`
///
/// # Arguments
///
/// * `address`: An IP address (IPv4 or IPv6) that needs to be truncated to its network address.
///   - **Type:** IP address field (e.g., `ip.src`, `ip.dst`).
///   - **Constraint:** This parameter **must** be a field reference and **cannot** be a literal string.
///     The engine dynamically evaluates the IP address from the request's context.
///
/// * `ipv4_network_bits`: An integer specifying the number of leading bits that represent the network
///   portion for an **IPv4** address. This value defines the equivalent of an IPv4 subnet mask.
///   - **Type:** `Integer`
///   - **Constraint:** Must be between `1` and `32`.
///
/// * `ipv6_network_bits`: An integer specifying the number of leading bits that represent the network
///   portion for an **IPv6** address. This value defines the equivalent of an IPv6 prefix length.
///   - **Type:** `Integer`
///   - **Constraint:** Must be between `1` and `128`.
///
/// # Returns
///
/// * **Type:** IP address (IPv4 or IPv6)
/// * **Description:** The calculated network address (network ID) corresponding to the input `address`
///   and the relevant network bit length. The host portion of the IP address is "zeroed out".
///
/// # How it Works
///
/// The `cidr` function intelligently processes the `address` parameter based on its type:
/// - If `address` resolves to an IPv4 address, the `ipv4_network_bits` parameter is used
///   to determine the network portion, and `ipv6_network_bits` is ignored.
/// - If `address` resolves to an IPv6 address, the `ipv6_network_bits` parameter is used
///   to determine the network portion, and `ipv4_network_bits` is ignored.
///
/// # Examples for Cloudflare Ruleset Engine Expressions
///
/// Below are examples of how `cidr` is used within actual Cloudflare Ruleset Engine expressions.
/// These are typically part of a larger rule definition.
///
/// **1. Matching IPv4 traffic from the `113.10.0.0/24` network:**
///
/// ```text
/// (cidr(ip.src, 24, 64) eq 113.10.0.0)
/// ```
/// *Explanation:* This expression checks if the source IP address (`ip.src`), when its network
/// portion is truncated to 24 bits (for IPv4), matches `113.10.0.0`. The `64` for
/// `ipv6_network_bits` is a placeholder and would be ignored if `ip.src` is IPv4.
///
/// **2. Matching IPv6 traffic from the `2001:0:0:0::/24` network:**
///
/// ```text
/// (cidr(ip.src, 32, 24) eq 2001:0000:0000:0000:0000:0000:0000:0000)
/// ```
/// *Explanation:* This expression checks if the source IP address (`ip.src`), when its network
/// portion is truncated to 24 bits (for IPv6), matches `2001:0000:0000:0000:0000:0000:0000:0000`.
/// The `32` for `ipv4_network_bits` is a placeholder and would be ignored if `ip.src` is IPv6.
///
/// **3. Blocking all traffic originating from a specific IPv4 subnet:**
///
/// ```text
/// (ip.src in { "192.168.1.0/24" }) or (cidr(ip.src, 24, 0) eq 10.0.0.0)
/// ```
/// *Explanation:* This example shows how to combine `in` operator with `cidr`. It would block
/// traffic from the `192.168.1.0/24` subnet directly or if the source IP address, when truncated
/// to a `/24`, matches `10.0.0.0`. Note that for `cidr` on IPv4, `ipv6_network_bits` can be
/// set to `0` as it will be ignored by the engine.
#[derive(Debug, Default)]
pub struct CIDRFunction {}

#[inline]
fn calc_ipv4_network_addr(ipv4_addr: Ipv4Addr, subnet_mask: i64) -> Ipv4Addr {
    let prefix_len_u32 = subnet_mask as u32;

    if prefix_len_u32 == 0 {
        return Ipv4Addr::new(0, 0, 0, 0);
    }

    let ip_as_u32: u32 = ipv4_addr.into();

    let shift_val = 32 - prefix_len_u32;

    let mask_u32 = u32::MAX << shift_val;

    Ipv4Addr::from(ip_as_u32 & mask_u32)
}

#[inline]
fn calc_ipv6_cidr_addr(ipv6_addr: Ipv6Addr, prefix_length: i64) -> Ipv6Addr {
    let prefix_len_u32 = prefix_length as u32;

    if prefix_len_u32 == 0 {
        return Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
    }

    let ip_as_u128: u128 = ipv6_addr.into();

    let shift_val = 128 - prefix_len_u32;
    let mask_u128 = if shift_val >= 128 {
        0
    } else {
        u128::MAX << shift_val
    };

    Ipv6Addr::from(ip_as_u128 & mask_u128)
}

#[inline]
fn cidr_impl<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let ip_res = args.next().expect("expected 3 args, got 0");
    let ipv4_subnet_mask_res = args.next().expect("expected 3 args, got 1");
    let ipv6_cidr = args.next().expect("expected 3 args, got 2");

    if args.next().is_some() {
        panic!("expected 3 arguments, got {}", 4 + args.count());
    }

    match (ip_res, ipv4_subnet_mask_res, ipv6_cidr) {
        (Ok(LhsValue::Ip(IpAddr::V4(ipv4_addr))), Ok(LhsValue::Int(subnet_mask)), _) => Some(
            LhsValue::Ip(IpAddr::V4(calc_ipv4_network_addr(ipv4_addr, subnet_mask))),
        ),
        (Ok(LhsValue::Ip(IpAddr::V6(ipv6_addr))), _, Ok(LhsValue::Int(prefix_length))) => Some(
            LhsValue::Ip(IpAddr::V6(calc_ipv6_cidr_addr(ipv6_addr, prefix_length))),
        ),
        (Err(Type::Ip), _, _) => return None,
        (_, Err(Type::Int), _) => return None,
        (_, _, Err(Type::Int)) => return None,
        _ => unreachable!(),
    }
}

impl FunctionDefinition for CIDRFunction {
    fn check_param(
        &self,
        _: &crate::ParserSettings,
        params: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        next_param: &super::FunctionParam<'_>,
        _: Option<&mut super::FunctionDefinitionContext>,
    ) -> Result<(), super::FunctionParamError> {
        match params.len() {
            0 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Field)?;
                next_param.expect_val_type(iter::once(Type::Ip.into()))?;
            }
            1 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Literal)?;
                next_param.expect_val_type(iter::once(Type::Int.into()))?;
            }
            2 => {
                next_param.expect_arg_kind(super::FunctionArgKind::Literal)?;
                next_param.expect_val_type(iter::once(Type::Int.into()))?;
            }
            _ => unreachable!(),
        }

        Ok(())
    }

    fn return_type(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<&super::FunctionDefinitionContext>,
    ) -> Type {
        Type::Ip
    }

    fn arg_count(&self) -> (usize, Option<usize>) {
        (3, Some(0))
    }

    fn compile(
        &self,
        _: &mut dyn ExactSizeIterator<Item = super::FunctionParam<'_>>,
        _: Option<super::FunctionDefinitionContext>,
    ) -> Box<dyn for<'i, 'a> Fn(FunctionArgs<'i, 'a>) -> Option<LhsValue<'a>> + Sync + Send + 'static>
    {
        Box::new(cidr_impl)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    // std::borrow::Cow is not used in these tests, can be removed if not used elsewhere in this module's tests.

    #[test]
    fn test_calc_ipv4_network_addr_fn() {
        let mut ipv4_addr = Ipv4Addr::new(192, 168, 2, 10);
        let mut subnet_mask = 24;

        let mut ip4_network_addr = calc_ipv4_network_addr(ipv4_addr, subnet_mask);
        assert_eq!(ip4_network_addr, Ipv4Addr::new(192, 168, 2, 0));

        ipv4_addr = Ipv4Addr::new(192, 168, 255, 50);
        subnet_mask = 23;
        ip4_network_addr = calc_ipv4_network_addr(ipv4_addr, subnet_mask);
        assert_eq!(ip4_network_addr, Ipv4Addr::new(192, 168, 254, 0));
    }

    #[test]
    fn test_calc_ipv6_cidr_addr() {
        // Test case 1: /64 prefix
        let ipv6_addr_1 = Ipv6Addr::new(
            0x2001, 0x0db8, 0xabcd, 0x0012, 0x3456, 0x7890, 0x0000, 0x0001,
        );
        let prefix_length_1: i64 = 64;
        let network_addr_1 = calc_ipv6_cidr_addr(ipv6_addr_1, prefix_length_1);
        assert_eq!(
            network_addr_1,
            Ipv6Addr::new(
                0x2001, 0x0db8, 0xabcd, 0x0012, 0x0000, 0x0000, 0x0000, 0x0000
            )
        );

        // Test case 2: /0 prefix (should result in ::)
        let ipv6_addr_2 = Ipv6Addr::new(
            0x2001, 0x0db8, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000, 0x0001,
        );
        let prefix_length_2: i64 = 0;
        let network_addr_2 = calc_ipv6_cidr_addr(ipv6_addr_2, prefix_length_2);
        assert_eq!(network_addr_2, Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0));

        // Test case 3: /128 prefix (should result in the same address)
        let ipv6_addr_3 = Ipv6Addr::new(
            0x2001, 0x0db8, 0x1234, 0x5678, 0x9abc, 0xdef0, 0x1234, 0x5678,
        );
        let prefix_length_3: i64 = 128;
        let network_addr_3 = calc_ipv6_cidr_addr(ipv6_addr_3, prefix_length_3);
        assert_eq!(network_addr_3, ipv6_addr_3);

        // Test case 4: /48 prefix
        let ipv6_addr_4 = Ipv6Addr::new(
            0x2001, 0x0db8, 0xacad, 0x1234, 0x5678, 0x9012, 0x3456, 0x789a,
        );
        let prefix_length_4: i64 = 48;
        let network_addr_4 = calc_ipv6_cidr_addr(ipv6_addr_4, prefix_length_4);
        assert_eq!(
            network_addr_4,
            Ipv6Addr::new(
                0x2001, 0x0db8, 0xacad, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000
            )
        );

        // Test case 5: A prefix that isn't a multiple of 16, e.g. /50
        let ipv6_addr_5 = Ipv6Addr::new(
            0x2001, 0x0db8, 0xacad, 0x1234, 0x5678, 0x9012, 0x3456, 0x789a,
        );
        let prefix_length_5: i64 = 50;
        let network_addr_5 = calc_ipv6_cidr_addr(ipv6_addr_5, prefix_length_5);
        assert_eq!(
            network_addr_5,
            Ipv6Addr::new(
                0x2001, 0x0db8, 0xacad, 0x0000, 0x0000, 0x0000, 0x0000, 0x0000
            )
        );
    }

    #[test]
    fn test_cidr_impl() {
        // Valid IPv4
        let ipv4_addr = Ipv4Addr::new(192, 168, 1, 100);
        let ipv4_prefix = 24;
        let expected_ipv4_net = Ipv4Addr::new(192, 168, 1, 0);
        let mut args_ipv4 = vec![
            Ok(LhsValue::Ip(IpAddr::V4(ipv4_addr))),
            Ok(LhsValue::Int(ipv4_prefix)),
            Ok(LhsValue::Int(64)),
        ]
        .into_iter();
        assert_eq!(
            cidr_impl(&mut args_ipv4),
            Some(LhsValue::Ip(IpAddr::V4(expected_ipv4_net)))
        );

        // Valid IPv4 with prefix 0
        let ipv4_addr_p0 = Ipv4Addr::new(192, 168, 1, 100);
        let ipv4_prefix_p0 = 0;
        let expected_ipv4_net_p0 = Ipv4Addr::new(0, 0, 0, 0);
        let mut args_ipv4_p0 = vec![
            Ok(LhsValue::Ip(IpAddr::V4(ipv4_addr_p0))),
            Ok(LhsValue::Int(ipv4_prefix_p0)),
            Ok(LhsValue::Int(64)), // Ignored
        ]
        .into_iter();
        assert_eq!(
            cidr_impl(&mut args_ipv4_p0),
            Some(LhsValue::Ip(IpAddr::V4(expected_ipv4_net_p0)))
        );

        // Valid IPv6
        let ipv6_addr = Ipv6Addr::new(
            0x2001, 0xdb8, 0xabcd, 0x0012, 0x3456, 0x7890, 0x0000, 0x0001,
        );
        let ipv6_prefix = 64;
        let expected_ipv6_net = Ipv6Addr::new(
            0x2001, 0xdb8, 0xabcd, 0x0012, 0x0000, 0x0000, 0x0000, 0x0000,
        );
        let mut args_ipv6 = vec![
            Ok(LhsValue::Ip(IpAddr::V6(ipv6_addr))),
            Ok(LhsValue::Int(24)), // Ignored IPv4 prefix, provide a valid type
            Ok(LhsValue::Int(ipv6_prefix)),
        ]
        .into_iter();
        assert_eq!(
            cidr_impl(&mut args_ipv6),
            Some(LhsValue::Ip(IpAddr::V6(expected_ipv6_net)))
        );

        // Valid IPv6 with prefix 0
        let ipv6_addr_p0 = Ipv6Addr::new(
            0x2001, 0xdb8, 0xabcd, 0x0012, 0x3456, 0x7890, 0x0000, 0x0001,
        );
        let ipv6_prefix_p0 = 0;
        let expected_ipv6_net_p0 = Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0);
        let mut args_ipv6_p0 = vec![
            Ok(LhsValue::Ip(IpAddr::V6(ipv6_addr_p0))),
            Ok(LhsValue::Int(24)), // Ignored
            Ok(LhsValue::Int(ipv6_prefix_p0)),
        ]
        .into_iter();
        assert_eq!(
            cidr_impl(&mut args_ipv6_p0),
            Some(LhsValue::Ip(IpAddr::V6(expected_ipv6_net_p0)))
        );

        // --- Error propagation (field lookup failed, returns None) ---
        // First arg (IP) is Err
        let mut args_err_ip =
            vec![Err(Type::Ip), Ok(LhsValue::Int(24)), Ok(LhsValue::Int(64))].into_iter();
        assert_eq!(cidr_impl(&mut args_err_ip), None);

        // Second arg (IPv4 prefix) is Err
        let mut args_err_ipv4_prefix = vec![
            Ok(LhsValue::Ip(IpAddr::V4(Ipv4Addr::new(10, 0, 0, 1)))),
            Err(Type::Int),
            Ok(LhsValue::Int(64)),
        ]
        .into_iter();
        assert_eq!(cidr_impl(&mut args_err_ipv4_prefix), None);

        // Third arg (IPv6 prefix) is Err - relevant for IPv6 case
        let mut args_err_ipv6_prefix = vec![
            Ok(LhsValue::Ip(IpAddr::V6(Ipv6Addr::new(
                0x2001, 0xdb8, 0, 0, 0, 0, 0, 1,
            )))),
            Ok(LhsValue::Int(24)), // This is ignored but must be valid for the match arm
            Err(Type::Int),
        ]
        .into_iter();
        assert_eq!(cidr_impl(&mut args_err_ipv6_prefix), None);
    }

    // --- Argument count panics ---
    #[test]
    #[should_panic(expected = "expected 3 args, got 0")]
    fn test_cidr_impl_panic_0_args() {
        let mut args = vec![].into_iter();
        cidr_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 3 args, got 1")]
    fn test_cidr_impl_panic_1_arg() {
        let mut args = vec![Ok(LhsValue::Ip(IpAddr::V4(Ipv4Addr::LOCALHOST)))].into_iter();
        cidr_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 3 args, got 2")]
    fn test_cidr_impl_panic_2_args() {
        let mut args = vec![
            Ok(LhsValue::Ip(IpAddr::V4(Ipv4Addr::LOCALHOST))),
            Ok(LhsValue::Int(24)),
        ]
        .into_iter();
        cidr_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "expected 3 arguments, got 4")]
    fn test_cidr_impl_panic_4_args() {
        let mut args = vec![
            Ok(LhsValue::Ip(IpAddr::V4(Ipv4Addr::LOCALHOST))),
            Ok(LhsValue::Int(24)),
            Ok(LhsValue::Int(64)),
            Ok(LhsValue::Int(0)), // Extra arg
        ]
        .into_iter();
        cidr_impl(&mut args);
    }

    // --- Type mismatch panics (unreachable!) ---
    // These test cases will hit the `_ => unreachable!()` arm if the
    // LhsValue variant is not what's expected by the success patterns,
    // and not an Err(Type::...) caught by the error patterns.
    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_cidr_impl_panic_bad_ip_type() {
        let mut args = vec![
            Ok(LhsValue::Bool(true)), // Not an IP
            Ok(LhsValue::Int(24)),
            Ok(LhsValue::Int(64)),
        ]
        .into_iter();
        cidr_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_cidr_impl_panic_bad_ipv4_prefix_type() {
        let mut args = vec![
            Ok(LhsValue::Ip(IpAddr::V4(Ipv4Addr::LOCALHOST))),
            Ok(LhsValue::Bool(true)), // Not an Int
            Ok(LhsValue::Int(64)),
        ]
        .into_iter();
        cidr_impl(&mut args);
    }

    #[test]
    #[should_panic(expected = "internal error: entered unreachable code")]
    fn test_cidr_impl_panic_bad_ipv6_prefix_type() {
        let mut args = vec![
            Ok(LhsValue::Ip(IpAddr::V6(Ipv6Addr::LOCALHOST))),
            Ok(LhsValue::Int(24)),    // Ignored ipv4 prefix, must be Int
            Ok(LhsValue::Bool(true)), // Not an Int
        ]
        .into_iter();
        cidr_impl(&mut args);
    }
}
