use context::{Context, Filter, RhsValue, Type};

use cidr::{Cidr, IpCidr};
use std::cmp::Ordering;
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

extern "C" {
    fn memmem(
        haystack: *const u8,
        haystack_len: usize,
        needle: *const u8,
        needle_len: usize,
    ) -> *const u8;
}

fn bytes_contains<T1: AsRef<[u8]>, T2: AsRef<[u8]>>(lhs: T1, rhs: T2) -> bool {
    let lhs = lhs.as_ref();
    let rhs = rhs.as_ref();

    unsafe { !memmem(lhs.as_ptr(), lhs.len(), rhs.as_ptr(), rhs.len()).is_null() }
}

fn bytes_ordering<T1: AsRef<[u8]>, T2: AsRef<[u8]>>(lhs: T1, rhs: T2) -> Ordering {
    lhs.as_ref().cmp(rhs.as_ref())
}

fn range_order<T: Ord>(lhs: T, rhs_first: T, rhs_last: T) -> Ordering {
    match (lhs.cmp(&rhs_first), lhs.cmp(&rhs_last)) {
        (Ordering::Less, _) => Ordering::Less,
        (_, Ordering::Greater) => Ordering::Greater,
        _ => Ordering::Equal,
    }
}

fn ip_order<T>(lhs: &T::Address, rhs: &T) -> Ordering
where
    T: Cidr,
    T::Address: Ord,
{
    range_order(lhs, &rhs.first_address(), &rhs.last_address())
}

impl PartialEq<RhsValue> for LhsValue {
    fn eq(&self, other: &RhsValue) -> bool {
        self.partial_cmp(other) == Some(Ordering::Equal)
    }
}

impl PartialOrd<RhsValue> for LhsValue {
    fn partial_cmp(&self, other: &RhsValue) -> Option<Ordering> {
        Some(match (self, other) {
            (
                &LhsValue::IpAddr(IpAddr::V4(ref addr)),
                &RhsValue::IpCidr(IpCidr::V4(ref network)),
            ) => ip_order(addr, network),
            (
                &LhsValue::IpAddr(IpAddr::V6(ref addr)),
                &RhsValue::IpCidr(IpCidr::V6(ref network)),
            ) => ip_order(addr, network),
            (&LhsValue::Unsigned(lhs), &RhsValue::Unsigned(ref rhs)) => lhs.cmp(rhs),
            (&LhsValue::Bytes(ref lhs), &RhsValue::Bytes(ref rhs)) => bytes_ordering(lhs, rhs),
            (&LhsValue::String(ref lhs), &RhsValue::String(ref rhs)) => bytes_ordering(lhs, rhs),
            (&LhsValue::Bytes(ref lhs), &RhsValue::String(ref rhs)) => bytes_ordering(lhs, rhs),
            (&LhsValue::String(ref lhs), &RhsValue::Bytes(ref rhs)) => bytes_ordering(lhs, rhs),
            _ => return None,
        })
    }
}

fn exec_op(lhs: &LhsValue, op: ::op::ComparisonOp, rhs: RhsValue) -> Option<bool> {
    use op::ComparisonOp::*;
    use op::MatchingOp;

    match op {
        Ordering(op) => lhs.partial_cmp(&rhs)
            .map(|ordering| op.contains(ordering.into())),

        Matching(op) => Some(match (lhs, op, rhs) {
            (&LhsValue::String(ref lhs), MatchingOp::Matches, RhsValue::String(ref rhs)) => {
                unimplemented!(
                    "Missing regexp implementation to match {:?} against {:?}",
                    lhs,
                    rhs
                )
            }
            (&LhsValue::Unsigned(lhs), MatchingOp::BitwiseAnd, RhsValue::Unsigned(rhs)) => {
                (lhs & rhs) != 0
            }
            (&LhsValue::Bytes(ref lhs), MatchingOp::Contains, RhsValue::Bytes(ref rhs)) => {
                bytes_contains(lhs, rhs)
            }
            (&LhsValue::String(ref lhs), MatchingOp::Contains, RhsValue::String(ref rhs)) => {
                bytes_contains(lhs, rhs)
            }
            (&LhsValue::Bytes(ref lhs), MatchingOp::Contains, RhsValue::String(ref rhs)) => {
                bytes_contains(lhs, rhs)
            }
            (&LhsValue::String(ref lhs), MatchingOp::Contains, RhsValue::Bytes(ref rhs)) => {
                bytes_contains(lhs, rhs)
            }
            _ => return None,
        }),
    }
}

impl<'i> Context<'i> for &'i ExecutionContext {
    type LhsValue = &'i LhsValue;
    type Filter = bool;

    fn get_field(self, path: &str) -> Option<&'i LhsValue> {
        self.0.get(path)
    }

    fn compare(self, lhs: &LhsValue, op: ::op::ComparisonOp, rhs: RhsValue) -> Result<bool, Type> {
        exec_op(lhs, op, rhs).ok_or_else(|| match *lhs {
            LhsValue::IpAddr(IpAddr::V4(_)) => Type::IpAddrV4,
            LhsValue::IpAddr(IpAddr::V6(_)) => Type::IpAddrV6,
            LhsValue::Bytes(_) => Type::Bytes,
            LhsValue::Unsigned(_) => Type::Unsigned,
            LhsValue::String(_) => Type::String,
        })
    }

    fn one_of<I: Iterator<Item = RhsValue>>(self, lhs: &LhsValue, rhs: I) -> Result<bool, Type> {
        let mut acc = true;
        for rhs in rhs {
            acc |= self.compare(
                lhs,
                ::op::ComparisonOp::Ordering(::op::OrderingMask::EQUAL),
                rhs,
            )?;
        }
        Ok(acc)
    }
}

impl Filter for bool {
    fn combine(self, op: ::op::CombiningOp, other: bool) -> bool {
        use op::CombiningOp::*;

        match op {
            And => self && other,
            Or => self || other,
            Xor => self != other,
        }
    }

    fn unary(self, op: ::op::UnaryOp) -> bool {
        use op::UnaryOp::*;

        match op {
            Not => !self,
        }
    }
}
