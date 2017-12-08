use context::Context;
use filter::{RhsValue, Type};

use cidr::{Cidr, IpCidr};
use std::collections::HashMap;
use std::net::IpAddr;

#[derive(Default)]
pub struct ExecutionContext(HashMap<String, LhsValue>);

impl ExecutionContext {
    pub fn new(map: HashMap<String, LhsValue>) -> Self {
        ExecutionContext(map)
    }
}

nested_enum!(#[derive(Debug, Clone)] LhsValue {
    IpAddr(IpAddr),
    Bytes(Vec<u8>),
    Unsigned(u64),
    String(String),
});

fn simple_op<T: Ord + Copy>(lhs: T, op: ::op::OrderingOp, rhs: T) -> Option<bool> {
    range_op(lhs, op, rhs, rhs)
}

extern "C" {
    fn memmem(
        haystack: *const u8,
        haystack_len: usize,
        needle: *const u8,
        needle_len: usize,
    ) -> *const u8;
}

fn bytes_op<T1: AsRef<[u8]>, T2: AsRef<[u8]>>(
    lhs: T1,
    op: ::op::ComparisonOp,
    rhs: T2,
) -> Option<bool> {
    use op::ComparisonOp::*;

    let lhs = lhs.as_ref();
    let rhs = rhs.as_ref();

    match op {
        Matching(::op::MatchingOp::Contains) => Some(unsafe {
            !memmem(lhs.as_ptr(), lhs.len(), rhs.as_ptr(), rhs.len()).is_null()
        }),
        Ordering(op) => simple_op(lhs, op, rhs),
        _ => None,
    }
}

fn range_op<T: Ord>(lhs: T, op: ::op::OrderingOp, rhs_first: T, rhs_last: T) -> Option<bool> {
    use op::OrderingOp::*;

    Some(match op {
        Equal => lhs >= rhs_first && lhs <= rhs_last,
        NotEqual => lhs < rhs_first || lhs > rhs_last,
        GreaterThanEqual => lhs >= rhs_last,
        LessThanEqual => lhs <= rhs_first,
        GreaterThan => lhs > rhs_last,
        LessThan => lhs < rhs_first,
    })
}

impl<'i> Context<'i> for &'i ExecutionContext {
    type LhsValue = &'i LhsValue;
    type Filter = bool;

    fn get_field(self, path: &str) -> Option<&'i LhsValue> {
        self.0.get(path)
    }

    fn compare(self, lhs: &LhsValue, op: ::op::ComparisonOp, rhs: RhsValue) -> Result<bool, Type> {
        use op::ComparisonOp::*;
        use op::MatchingOp;

        (match (lhs, op, rhs) {
            (
                &LhsValue::String(ref lhs),
                Matching(MatchingOp::Matches),
                RhsValue::String(ref rhs),
            ) => unimplemented!(
                "Missing regexp implementation to match {:?} against {:?}",
                lhs,
                rhs
            ),
            (
                &LhsValue::IpAddr(IpAddr::V4(ref addr)),
                Ordering(op),
                RhsValue::IpCidr(IpCidr::V4(ref network)),
            ) => range_op(addr, op, &network.first_address(), &network.last_address()),
            (
                &LhsValue::IpAddr(IpAddr::V6(ref addr)),
                Ordering(op),
                RhsValue::IpCidr(IpCidr::V6(ref network)),
            ) => range_op(addr, op, &network.first_address(), &network.last_address()),
            (
                &LhsValue::Unsigned(lhs),
                Matching(MatchingOp::BitwiseAnd),
                RhsValue::Unsigned(rhs),
            ) => Some((lhs & rhs) != 0),
            (&LhsValue::Unsigned(lhs), Ordering(op), RhsValue::Unsigned(rhs)) => {
                simple_op(lhs, op, rhs)
            }
            (&LhsValue::Bytes(ref lhs), op, RhsValue::Bytes(ref rhs)) => bytes_op(lhs, op, rhs),
            (&LhsValue::String(ref lhs), op, RhsValue::String(ref rhs)) => bytes_op(lhs, op, rhs),
            (&LhsValue::Bytes(ref lhs), op, RhsValue::String(ref rhs)) => bytes_op(lhs, op, rhs),
            (&LhsValue::String(ref lhs), op, RhsValue::Bytes(ref rhs)) => bytes_op(lhs, op, rhs),
            _ => None,
        }).ok_or_else(|| match *lhs {
            LhsValue::IpAddr(IpAddr::V4(_)) => Type::IpAddrV4,
            LhsValue::IpAddr(IpAddr::V6(_)) => Type::IpAddrV6,
            LhsValue::Bytes(_) => Type::Bytes,
            LhsValue::Unsigned(_) => Type::Unsigned,
            LhsValue::String(_) => Type::String,
        })
    }

    fn combine(self, lhs: bool, op: ::op::CombiningOp, rhs: bool) -> bool {
        use op::CombiningOp::*;

        match op {
            And => lhs && rhs,
            Or => lhs || rhs,
            Xor => lhs != rhs,
        }
    }

    fn unary(self, op: ::op::UnaryOp, arg: bool) -> bool {
        use op::UnaryOp::*;

        match op {
            Not => !arg,
        }
    }
}
