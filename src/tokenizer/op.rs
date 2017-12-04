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
    "and" | "&&" => And,
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
});

simple_enum!(UnaryOp {
    "not" | "!" => Not,
});
