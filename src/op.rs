simple_enum!(OrderingOp {
    "eq" | "==" => Equal,
    "ne" | "!=" => NotEqual,
    "ge" | ">=" => GreaterThanEqual,
    "le" | "<=" => LessThanEqual,
    "gt" | ">" => GreaterThan,
    "lt" | "<" => LessThan,
});

simple_enum!(MatchingOp {
    "contains" => Contains,
    "~" | "matches" => Matches,
    "&" | "bitwise_and" => BitwiseAnd,
});

nested_enum!(#[derive(Debug, PartialEq, Eq, Clone, Copy)] ComparisonOp {
    Ordering(OrderingOp),
    Matching(MatchingOp),
});

simple_enum!(CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

simple_enum!(UnaryOp {
    "not" | "!" => Not,
});
