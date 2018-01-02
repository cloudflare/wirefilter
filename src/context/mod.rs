use bytes::Bytes;
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

nested_enum!(#[derive(Debug)] RhsValue {
    IpCidr(IpCidr),
    Bytes(Bytes),
    Unsigned(u64),
});

impl RhsValue {
    pub fn get_type(&self) -> Type {
        match *self {
            RhsValue::IpCidr(IpCidr::V4(_)) => Type::IpAddrV4,
            RhsValue::IpCidr(IpCidr::V6(_)) => Type::IpAddrV6,
            RhsValue::Bytes(ref b) => if b.is_str() {
                Type::String
            } else {
                Type::Bytes
            },
            RhsValue::Unsigned(_) => Type::Unsigned,
        }
    }
}

pub trait Context<'i>: Copy {
    type LhsValue;
    type Filter: Filter;

    fn get_field(self, path: &'i str) -> Option<Self::LhsValue>;
    fn compare(
        self,
        lhs: Self::LhsValue,
        op: ComparisonOp,
        rhs: RhsValue,
    ) -> Result<Self::Filter, Type>;
    fn one_of<I: Iterator<Item = RhsValue>>(
        self,
        lhs: Self::LhsValue,
        rhs: I,
    ) -> Result<Self::Filter, Type>;
}

pub trait Filter: Sized {
    fn combine(self, op: CombiningOp, other: Self) -> Self;
    fn unary(self, op: UnaryOp) -> Self;
}

pub mod ast;
pub mod execution;
