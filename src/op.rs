mod ordering {
    use lex::{Lex, LexResult};

    use std::cmp::Ordering;

    simple_enum!(OrderingOp {
        "eq" | "==" => Equal,
        "ne" | "!=" => NotEqual,
        "ge" | ">=" => GreaterThanEqual,
        "le" | "<=" => LessThanEqual,
        "gt" | ">" => GreaterThan,
        "lt" | "<" => LessThan,
    });

    bitflags! {
        #[derive(Serialize, Deserialize)]
        pub struct OrderingMask: u8 {
            const LESS = 0b001;
            const GREATER = 0b010;
            const EQUAL = 0b100;
        }
    }

    impl From<Ordering> for OrderingMask {
        fn from(ordering: Ordering) -> Self {
            match ordering {
                Ordering::Equal => OrderingMask::EQUAL,
                Ordering::Greater => OrderingMask::GREATER,
                Ordering::Less => OrderingMask::LESS,
            }
        }
    }

    impl<'a> Lex<'a> for OrderingMask {
        fn lex(input: &str) -> LexResult<Self> {
            let (op, input) = OrderingOp::lex(input)?;
            Ok((
                match op {
                    OrderingOp::Equal => OrderingMask::EQUAL,
                    OrderingOp::NotEqual => OrderingMask::LESS | OrderingMask::GREATER,
                    OrderingOp::GreaterThanEqual => OrderingMask::GREATER | OrderingMask::EQUAL,
                    OrderingOp::LessThanEqual => OrderingMask::LESS | OrderingMask::EQUAL,
                    OrderingOp::GreaterThan => OrderingMask::GREATER,
                    OrderingOp::LessThan => OrderingMask::LESS,
                },
                input,
            ))
        }
    }
}

pub use self::ordering::OrderingMask;

simple_enum!(UnsignedOp {
    "&" | "bitwise_and" => BitwiseAnd,
});

simple_enum!(BytesOp {
    "contains" => Contains,
    "~" | "matches" => Matches,
});

nested_enum!(#[derive(Debug, PartialEq, Eq, Clone, Copy)] ComparisonOp {
    Any(OrderingMask),
    Unsigned(UnsignedOp),
    Bytes(BytesOp),
});

simple_enum!(CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

simple_enum!(UnaryOp {
    "not" | "!" => Not,
});
