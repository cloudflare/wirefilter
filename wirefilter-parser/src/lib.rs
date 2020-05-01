pub mod ast;

use pest_consume::{match_nodes, Error, Parser as PestParser};

#[derive(PestParser)]
#[grammar = "./grammar.pest"]
pub struct Parser;

pub type ParseResult<T> = Result<T, Error<Rule>>;
pub type Node<'i> = pest_consume::Node<'i, Rule, ()>;

#[pest_consume::parser]
impl Parser {
    fn variable_name(node: Node) -> ParseResult<ast::Var> {
        // TODO check in scheme
        Ok(ast::Var(node.as_str()))
    }

    fn int_literal(node: Node) -> ParseResult<ast::Rhs> {
        let mut num = match_nodes! {
            node.children();
            [dec_digits(d)] => d
        };

        if let Some('-') = node.as_str().chars().next() {
            num = -num;
        }

        Ok(ast::Rhs::Int(num))
    }

    fn dec_digits(node: Node) -> ParseResult<i32> {
        Ok(32)
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
    fn parse_variable_name() {
        assert_eq!(parse!(variable_name, "foo"), Ok(ast::Var("foo")));
        assert_eq!(parse!(variable_name, "f1o2o3"), Ok(ast::Var("f1o2o3")));

        assert_eq!(
            parse!(variable_name, "f1o2o3.bar321"),
            Ok(ast::Var("f1o2o3.bar321"))
        );

        assert_eq!(
            parse!(variable_name, "foo.bar.baz"),
            Ok(ast::Var("foo.bar.baz"))
        );

        assert!(parse!(variable_name, "123foo").is_err());
    }

    #[test]
    fn parse_int_literal() {
        assert_eq!(parse!(int_literal, "42"), Ok(ast::Rhs::Int(42)));
        assert_eq!(parse!(int_literal, "-42"), Ok(ast::Rhs::Int(-42)));
    }
}
