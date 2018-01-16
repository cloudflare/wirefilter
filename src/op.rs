use std::cmp::Ordering;

const LESS: u8 = 0b001;
const GREATER: u8 = 0b010;
const EQUAL: u8 = 0b100;

simple_enum!(#[repr(u8)] OrderingOp {
    "eq" | "==" => Equal = EQUAL,
    "ne" | "!=" => NotEqual = LESS | GREATER,
    "ge" | ">=" => GreaterThanEqual = GREATER | EQUAL,
    "le" | "<=" => LessThanEqual = LESS | EQUAL,
    "gt" | ">" => GreaterThan = GREATER,
    "lt" | "<" => LessThan = LESS,
});

impl OrderingOp {
    pub fn contains(self, ordering: Ordering) -> bool {
        let mask = self as u8;
        let flag = match ordering {
            Ordering::Less => LESS,
            Ordering::Greater => GREATER,
            Ordering::Equal => EQUAL,
        };
        mask & flag != 0
    }
}

simple_enum!(UnsignedOp {
    "&" | "bitwise_and" => BitwiseAnd,
});

simple_enum!(BytesOp {
    "contains" => Contains,
    "~" | "matches" => Matches,
});

nested_enum!(#[derive(Debug, PartialEq, Eq, Clone, Copy)] ComparisonOp {
    Any(OrderingOp),
    Unsigned(UnsignedOp),
    Bytes(BytesOp),
});

simple_enum!(#[derive(PartialOrd, Ord)] CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

simple_enum!(UnaryOp {
    "not" | "!" => Not,
});
