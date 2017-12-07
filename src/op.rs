simple_enum!(ComparisonOp {
    "eq" | "==" => Equal,
    "ne" | "!=" => NotEqual,
    "ge" | ">=" => GreaterThanEqual,
    "le" | "<=" => LessThanEqual,
    "gt" | ">" => GreaterThan,
    "lt" | "<" => LessThan,
    "contains" => Contains,
    "~" | "matches" => Matches,
    "&" | "bitwise_and" => BitwiseAnd,
});

simple_enum!(CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

simple_enum!(UnaryOp {
    "not" | "!" => Not,
});
