pub mod ast;

use pest::error::ErrorVariant;
use pest_consume::{match_nodes, Error as ParseError, Parser as PestParser};

#[derive(PestParser)]
#[grammar = "./grammar.pest"]
pub struct Parser;

pub type ParseResult<T> = Result<T, ParseError<Rule>>;
pub type Node<'i> = pest_consume::Node<'i, Rule, ()>;

trait IntoParseResult<T> {
    fn into_parse_result(self, node: &Node) -> ParseResult<T>;
}

impl<T, E> IntoParseResult<T> for Result<T, E>
where
    E: ToString,
{
    fn into_parse_result(self, node: &Node) -> ParseResult<T> {
        self.map_err(|e| {
            let span = node.as_span();

            let err_var = ErrorVariant::CustomError {
                message: e.to_string(),
            };

            ParseError::new_from_span(err_var, span)
        })
    }
}

macro_rules! parse_num {
    ($node:expr, $ty:ident, $radix:expr) => {
        $ty::from_str_radix($node.as_str(), $radix).into_parse_result(&$node)
    };
}

#[pest_consume::parser]
impl Parser {
    fn var(node: Node) -> ParseResult<ast::Var> {
        // TODO check in scheme
        Ok(ast::Var(node.as_str().into()))
    }

    fn int_lit(node: Node) -> ParseResult<ast::Int> {
        use Rule::*;

        let digits_node = node.children().single().unwrap();

        let radix = match digits_node.as_rule() {
            hex_digits => 16,
            oct_digits => 8,
            dec_digits => 10,
            _ => unreachable!(),
        };

        let mut num = parse_num!(digits_node, i32, radix)?;

        if let Some('-') = node.as_str().chars().next() {
            num = -num;
        }

        Ok(ast::Int(num))
    }

    fn esc_alias(node: Node) -> ParseResult<u8> {
        Ok(match node.as_str() {
            "\"" => b'"',
            "\\" => b'\\',
            "n" => b'\n',
            "r" => b'\r',
            "t" => b'\t',
            _ => unreachable!(),
        })
    }

    fn str_lit(node: Node) -> ParseResult<ast::Bytes> {
        use Rule::*;

        let content = node.into_children().collect::<Vec<_>>();

        // NOTE: if there are no escapes then we can avoid allocating.
        if content.len() == 1 && matches!(content[0].as_rule(), Rule::text) {
            return Ok(ast::Bytes(content[0].as_str().as_bytes().into()));
        }

        let mut s = Vec::new();

        for node in content {
            match node.as_rule() {
                text => s.extend_from_slice(node.as_str().as_bytes()),
                esc_alias => s.push(Parser::esc_alias(node)?),
                esc_hex_byte => s.push(parse_num!(node, u8, 16)?),
                _ => unreachable!(),
            }
        }

        Ok(ast::Bytes(s.into()))
    }

    fn int_range(node: Node) -> ParseResult<ast::IntRangeInclusive> {
        match_nodes! {
            node.children();
            [int_lit(i1), int_lit(i2)] => if i2.0 < i1.0 {
                Err("incompatible range bounds").into_parse_result(&node)
            } else {
                Ok(ast::IntRangeInclusive(i1.0..=i2.0))
            }
        }
    }

    fn rhs(node: Node) -> ParseResult<ast::Rhs> {
        Ok(match_nodes! {
            node.children();
            [int_lit(i)] => ast::Rhs::Int(i),
            [int_range(r)] => ast::Rhs::IntRangeInclusive(r)
        })
    }

    fn bin_op(node: Node) -> ParseResult<ast::BinOp> {
        use ast::BinOp::*;
        use Rule::*;

        let op = node.children().single().unwrap().as_rule();

        Ok(match op {
            eq_op => Eq,
            ne_op => NotEq,
            ge_op => GreaterOrEq,
            le_op => LessOrEq,
            gt_op => Greater,
            lt_op => Less,
            band_op => BitwiseAnd,
            contains_op => Contains,
            matches_op => Matches,
            in_op => In,
            _ => unreachable!(),
        })
    }

    fn expr(node: Node) -> ParseResult<ast::Expr> {
        // TODO type checks
        Ok(match_nodes! {
            node.children();
            [var(var), bin_op(op), rhs(rhs)] => ast::Expr::Binary {lhs: var, op, rhs},
            [var(var)] => ast::Expr::Unary(var)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parse {
        ($rule:ident, $input:expr) => {
            Parser::parse(Rule::$rule, $input)
                .and_then(|p| p.single())
                .and_then(Parser::$rule)
        };
    }

    #[test]
    fn parse_var() {
        assert_eq!(parse!(var, "foo"), Ok(ast::Var("foo".into())));
        assert_eq!(parse!(var, "f1o2o3"), Ok(ast::Var("f1o2o3".into())));
        assert_eq!(
            parse!(var, "f1o2o3.bar321"),
            Ok(ast::Var("f1o2o3.bar321".into()))
        );
        assert_eq!(
            parse!(var, "foo.bar.baz"),
            Ok(ast::Var("foo.bar.baz".into()))
        );
        assert!(parse!(var, "123foo").is_err());
    }

    #[test]
    fn parse_int_lit() {
        assert_eq!(parse!(int_lit, "42"), Ok(ast::Int(42)));
        assert_eq!(parse!(int_lit, "-42"), Ok(ast::Int(-42)));
        assert_eq!(parse!(int_lit, "0x2A"), Ok(ast::Int(42)));
        assert_eq!(parse!(int_lit, "-0x2a"), Ok(ast::Int(-42)));
        assert_eq!(parse!(int_lit, "052"), Ok(ast::Int(42)));
        assert_eq!(parse!(int_lit, "-052"), Ok(ast::Int(-42)));
        assert!(parse!(int_lit, "-abc").is_err());
        assert!(parse!(int_lit, "99999999999999999999999999999").is_err());
    }

    #[test]
    fn parse_int_range() {
        assert_eq!(
            parse!(int_range, "42..0x2b"),
            Ok(ast::IntRangeInclusive(42..=43))
        );

        assert_eq!(
            parse!(int_range, "-0x2a..0x2A"),
            Ok(ast::IntRangeInclusive(-42..=42))
        );

        assert_eq!(
            parse!(int_range, "42..42"),
            Ok(ast::IntRangeInclusive(42..=42))
        );

        assert!(parse!(int_range, "42 ..43").is_err());
        assert!(parse!(int_range, "42.. 43").is_err());
        assert!(parse!(int_range, "45..42").is_err());
        assert!(parse!(int_range, "42..z").is_err());
    }

    #[test]
    fn parse_str_lit() {
        assert_eq!(
            parse!(str_lit, r#""""#),
            Ok(ast::Bytes("".as_bytes().into()))
        );

        assert_eq!(
            parse!(str_lit, r#""foobar baz  qux""#),
            Ok(ast::Bytes("foobar baz  qux".as_bytes().into()))
        );

        assert_eq!(
            parse!(str_lit, r#""\n foo \t\r \\ baz \" bar ""#),
            Ok(ast::Bytes("\n foo \t\r \\ baz \" bar ".as_bytes().into()))
        );

        assert_eq!(
            parse!(str_lit, r#""foo \x41\x42 bar\x43""#),
            Ok(ast::Bytes("foo AB barC".as_bytes().into()))
        );

        assert!(parse!(str_lit, r#""foobar \i""#).is_err());
        assert!(parse!(str_lit, r#""foobar \x3z""#).is_err());
    }

    #[test]
    fn parse_bin_op() {
        assert_eq!(parse!(bin_op, "=="), Ok(ast::BinOp::Eq));
        assert_eq!(parse!(bin_op, "eq"), Ok(ast::BinOp::Eq));
        assert_eq!(parse!(bin_op, "!="), Ok(ast::BinOp::NotEq));
        assert_eq!(parse!(bin_op, "ne"), Ok(ast::BinOp::NotEq));
        assert_eq!(parse!(bin_op, ">="), Ok(ast::BinOp::GreaterOrEq));
        assert_eq!(parse!(bin_op, "ge"), Ok(ast::BinOp::GreaterOrEq));
        assert_eq!(parse!(bin_op, "<="), Ok(ast::BinOp::LessOrEq));
        assert_eq!(parse!(bin_op, "le"), Ok(ast::BinOp::LessOrEq));
        assert_eq!(parse!(bin_op, ">"), Ok(ast::BinOp::Greater));
        assert_eq!(parse!(bin_op, "gt"), Ok(ast::BinOp::Greater));
        assert_eq!(parse!(bin_op, "<"), Ok(ast::BinOp::Less));
        assert_eq!(parse!(bin_op, "lt"), Ok(ast::BinOp::Less));
        assert_eq!(parse!(bin_op, "&"), Ok(ast::BinOp::BitwiseAnd));
        assert_eq!(parse!(bin_op, "bitwise_and "), Ok(ast::BinOp::BitwiseAnd));
        assert_eq!(parse!(bin_op, "contains "), Ok(ast::BinOp::Contains));
        assert_eq!(parse!(bin_op, "~ "), Ok(ast::BinOp::Matches));
        assert_eq!(parse!(bin_op, "matches "), Ok(ast::BinOp::Matches));
        assert_eq!(parse!(bin_op, "in"), Ok(ast::BinOp::In));
    }

    #[test]
    fn parse_expr() {
        assert_eq!(
            parse!(expr, "foo.bar.baz"),
            Ok(ast::Expr::Unary(ast::Var("foo.bar.baz".into())))
        );

        assert_eq!(
            parse!(expr, "foo.bar.baz in 32..42"),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo.bar.baz".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::IntRangeInclusive(ast::IntRangeInclusive(32..=42))
            })
        );
    }
}
