use super::{CombiningOp, ComparisonOp, Context, RhsValue, Type, UnaryOp};

use cidr::{Cidr, IpCidr};
use std::collections::HashMap;
use std::net::IpAddr;

#[derive(Default)]
pub struct ExecutionContext(HashMap<String, LhsValue>);

#[derive(Debug, Clone)]
pub enum LhsValue {
    IpAddr(IpAddr),
    Bytes(Vec<u8>),
    Unsigned(u64),
    String(String),
}

fn simple_op<T: Ord + Copy>(lhs: T, op: ComparisonOp, rhs: T) -> Option<bool> {
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

fn bytes_op<T1: AsRef<[u8]>, T2: AsRef<[u8]>>(lhs: T1, op: ComparisonOp, rhs: T2) -> Option<bool> {
    let lhs = lhs.as_ref();
    let rhs = rhs.as_ref();

    if op == ComparisonOp::Contains {
        Some(unsafe {
            !memmem(lhs.as_ptr(), lhs.len(), rhs.as_ptr(), rhs.len()).is_null()
        })
    } else {
        simple_op(lhs, op, rhs)
    }
}

fn range_op<T: Ord>(lhs: T, op: ComparisonOp, rhs_first: T, rhs_last: T) -> Option<bool> {
    Some(match op {
        ComparisonOp::Equal => lhs >= rhs_first && lhs <= rhs_last,
        ComparisonOp::NotEqual => lhs < rhs_first || lhs > rhs_last,
        ComparisonOp::GreaterThanEqual => lhs >= rhs_last,
        ComparisonOp::LessThanEqual => lhs <= rhs_first,
        ComparisonOp::GreaterThan => lhs > rhs_last,
        ComparisonOp::LessThan => lhs < rhs_first,
        _ => return None,
    })
}

impl<'i> Context<'i> for &'i ExecutionContext {
    type LhsValue = &'i LhsValue;
    type Filter = bool;

    fn get_field(self, path: &str) -> Option<&'i LhsValue> {
        self.0.get(path)
    }

    fn compare(self, lhs: &LhsValue, op: ComparisonOp, rhs: RhsValue) -> Result<bool, Type> {
        (match (lhs, op, rhs) {
            (&LhsValue::String(ref lhs), ComparisonOp::Matches, RhsValue::String(ref rhs)) => {
                unimplemented!(
                    "Missing regexp implementation to match {:?} against {:?}",
                    lhs,
                    rhs
                )
            }
            (
                &LhsValue::IpAddr(IpAddr::V4(ref addr)),
                op,
                RhsValue::IpCidr(IpCidr::V4(ref network)),
            ) => range_op(addr, op, &network.first_address(), &network.last_address()),
            (
                &LhsValue::IpAddr(IpAddr::V6(ref addr)),
                op,
                RhsValue::IpCidr(IpCidr::V6(ref network)),
            ) => range_op(addr, op, &network.first_address(), &network.last_address()),
            (&LhsValue::Unsigned(lhs), ComparisonOp::BitwiseAnd, RhsValue::Unsigned(rhs)) => {
                Some((lhs & rhs) != 0)
            }
            (&LhsValue::Unsigned(lhs), op, RhsValue::Unsigned(rhs)) => simple_op(lhs, op, rhs),
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

    fn combine(self, lhs: bool, op: CombiningOp, rhs: bool) -> bool {
        match op {
            CombiningOp::And => lhs && rhs,
            CombiningOp::Or => lhs || rhs,
            CombiningOp::Xor => lhs != rhs,
        }
    }

    fn unary(self, op: UnaryOp, arg: bool) -> bool {
        match op {
            UnaryOp::Not => !arg,
        }
    }
}
