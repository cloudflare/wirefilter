use cidr::IpCidr;
use op::{CombiningOp, ComparisonOp, UnaryOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    IpAddrV4,
    IpAddrV6,
    Bytes,
    Unsigned,
    String,
}

nested_enum!(#[derive(Debug, Clone)] RhsValue {
    IpCidr(IpCidr),
    Bytes(Vec<u8>),
    Unsigned(u64),
    String(String),
});

impl RhsValue {
    pub fn get_type(&self) -> Type {
        match *self {
            RhsValue::IpCidr(IpCidr::V4(_)) => Type::IpAddrV4,
            RhsValue::IpCidr(IpCidr::V6(_)) => Type::IpAddrV6,
            RhsValue::Bytes(_) => Type::Bytes,
            RhsValue::Unsigned(_) => Type::Unsigned,
            RhsValue::String(_) => Type::String,
        }
    }
}

pub trait Context<'i>: Copy {
    type LhsValue;
    type Filter: Filter;

    fn get_field(self, path: &'i str) -> Option<Self::LhsValue>;
    fn compare(self, lhs: Self::LhsValue, op: ComparisonOp, rhs: RhsValue) -> Result<Self::Filter, Type>;
}

pub trait Filter: Sized {
    fn combine(self, op: CombiningOp, other: Self) -> Self;
    fn unary(self, op: UnaryOp) -> Self;
}

pub mod execution;
