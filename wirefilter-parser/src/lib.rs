pub mod ast;

use pest::error::ErrorVariant;
use pest_consume::{Error as ParseError, Parser as PestParser};
use std::error::Error;
use std::fmt::Display;

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
    E: Error + Display,
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

#[pest_consume::parser]
impl Parser {
    fn var(node: Node) -> ParseResult<ast::Var> {
        // TODO check in scheme
        Ok(ast::Var(node.as_str()))
    }

    fn int_lit(node: Node) -> ParseResult<ast::Rhs> {
        use Rule::*;

        let digits_node = node.children().single().unwrap();
        let digits_str = digits_node.as_str();

        let radix = match digits_node.as_rule() {
            hex_digits => 16,
            oct_digits => 8,
            dec_digits => 10,
            _ => unreachable!(),
        };

        let mut num = i32::from_str_radix(digits_str, radix).into_parse_result(&node)?;

        if let Some('-') = node.as_str().chars().next() {
            num = -num;
        }

        Ok(ast::Rhs::Int(num))
    }

    fn bin_op(node: Node) -> ParseResult<ast::BinOp> {
        use ast::BinOp::*;
        use Rule::*;

        let op = node.into_children().single().unwrap().as_rule();

        Ok(match op {
            gt_op => Greater,
            ne_op => NotEq,
            ge_op => GreaterOrEq,
            le_op => LessOrEq,
            band_op => BitwiseAnd,
            contains_op => Contains,
            matches_op => Matches,
            in_op => In,
            _ => unreachable!(),
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
        assert_eq!(parse!(var, "foo"), Ok(ast::Var("foo")));
        assert_eq!(parse!(var, "f1o2o3"), Ok(ast::Var("f1o2o3")));
        assert_eq!(parse!(var, "f1o2o3.bar321"), Ok(ast::Var("f1o2o3.bar321")));
        assert_eq!(parse!(var, "foo.bar.baz"), Ok(ast::Var("foo.bar.baz")));
        assert!(parse!(var, "123foo").is_err());
    }

    #[test]
    fn parse_int_lit() {
        assert_eq!(parse!(int_lit, "42"), Ok(ast::Rhs::Int(42)));
        assert_eq!(parse!(int_lit, "-42"), Ok(ast::Rhs::Int(-42)));
        assert_eq!(parse!(int_lit, "0x2A"), Ok(ast::Rhs::Int(42)));
        assert_eq!(parse!(int_lit, "-0x2a"), Ok(ast::Rhs::Int(-42)));
        assert_eq!(parse!(int_lit, "052"), Ok(ast::Rhs::Int(42)));
        assert_eq!(parse!(int_lit, "-052"), Ok(ast::Rhs::Int(-42)));
        assert!(parse!(int_lit, "-abc").is_err());
        assert!(parse!(int_lit, "99999999999999999999999999999").is_err());
    }
}
