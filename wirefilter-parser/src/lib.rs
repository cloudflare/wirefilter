pub mod ast;

use pest::error::ErrorVariant;
use pest_consume::{match_nodes, Error as ParseError, Parser as PestParser};
use std::error::Error;
use std::fmt::Display;

#[derive(PestParser)]
#[grammar = "./grammar.pest"]
pub struct Parser;

pub type ParseResult<T> = Result<T, ParseError<Rule>>;
pub type Node<'i> = pest_consume::Node<'i, Rule, ()>;

trait IntoParseResult<T> {
    fn into_parse_result(self, node: Node) -> ParseResult<T>;
}

impl<T, E> IntoParseResult<T> for Result<T, E>
where
    E: Error + Display,
{
    fn into_parse_result(self, node: Node) -> ParseResult<T> {
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
        let mut num = match_nodes! {
            node.children();
            [dec_digits(d)] => d,
            [oct_digits(d)] => d,
            [hex_digits(d)] => d
        };

        if let Some('-') = node.as_str().chars().next() {
            num = -num;
        }

        Ok(ast::Rhs::Int(num))
    }

    #[inline]
    fn dec_digits(node: Node) -> ParseResult<i32> {
        i32::from_str_radix(node.as_str(), 10).into_parse_result(node)
    }

    #[inline]
    fn oct_digits(node: Node) -> ParseResult<i32> {
        i32::from_str_radix(node.as_str(), 8).into_parse_result(node)
    }

    #[inline]
    fn hex_digits(node: Node) -> ParseResult<i32> {
        i32::from_str_radix(node.as_str(), 16).into_parse_result(node)
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
