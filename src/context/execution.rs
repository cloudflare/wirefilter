use super::{CombiningOp, ComparisonOp, Context, RhsValue, Type, UnaryOp};

use cidr::Cidr;
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

impl<'i> Context<'i> for &'i ExecutionContext {
    type LhsValue = &'i LhsValue;
    type Filter = bool;

    fn get_field(self, path: &str) -> Option<&'i LhsValue> {
        self.0.get(path)
    }

    fn compare(self, lhs: &LhsValue, op: ComparisonOp, rhs: RhsValue) -> Result<bool, Type> {
        Ok(match (lhs, op, rhs) {
            (&LhsValue::IpAddr(ref addr), ComparisonOp::Equal, RhsValue::IpCidr(ref network)) => {
                network.contains(addr)
            }
            _ => {
                return Err(match *lhs {
                    LhsValue::IpAddr(_) => Type::IpAddr,
                    LhsValue::Bytes(_) => Type::Bytes,
                    LhsValue::Unsigned(_) => Type::Unsigned,
                    LhsValue::String(_) => Type::String,
                });
            }
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
