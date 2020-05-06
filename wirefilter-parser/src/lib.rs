pub mod ast;
mod semantics;

use cidr::{Ipv4Cidr, Ipv6Cidr};
use pest::error::ErrorVariant;
use pest_consume::{match_nodes, Error as ParseError, Parser as PestParser};
use semantics::ValidateSemantics;
use std::borrow::Cow;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::ops::RangeInclusive;

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

macro_rules! parse_type {
    ($node:expr, $ty:ident) => {
        $node.as_str().parse::<$ty>().into_parse_result(&$node)
    };
}

macro_rules! parse_range {
    ($node:expr, $lit_ty:ident) => {
        match_nodes! {
            $node.children();
            [$lit_ty(l1), $lit_ty(l2)] => (l1..=l2).validate_semantics().into_parse_result(&$node)
        }
    };
}

#[pest_consume::parser]
impl Parser {
    fn var(node: Node) -> ParseResult<ast::Var> {
        // TODO check in scheme
        Ok(ast::Var(node.as_str().into()))
    }

    fn int_lit(node: Node) -> ParseResult<i32> {
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

        Ok(num)
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

    fn str_lit(node: Node) -> ParseResult<Cow<[u8]>> {
        use Rule::*;

        let content = node.into_children().collect::<Vec<_>>();

        // NOTE: if there are no escapes then we can avoid allocating.
        if content.len() == 1 && matches!(content[0].as_rule(), Rule::text) {
            return Ok(content[0].as_str().as_bytes().into());
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

        Ok(s.into())
    }

    fn int_range(node: Node) -> ParseResult<RangeInclusive<i32>> {
        parse_range!(node, int_lit)
    }

    #[inline]
    fn ipv4_lit(node: Node) -> ParseResult<Ipv4Addr> {
        parse_type!(node, Ipv4Addr)
    }

    #[inline]
    fn ipv6_lit(node: Node) -> ParseResult<Ipv6Addr> {
        parse_type!(node, Ipv6Addr)
    }

    #[inline]
    fn ipv4_cidr(node: Node) -> ParseResult<Ipv4Cidr> {
        parse_type!(node, Ipv4Cidr)
    }

    #[inline]
    fn ipv6_cidr(node: Node) -> ParseResult<Ipv6Cidr> {
        parse_type!(node, Ipv6Cidr)
    }

    fn ipv4_range(node: Node) -> ParseResult<RangeInclusive<Ipv4Addr>> {
        parse_range!(node, ipv4_lit)
    }

    fn ipv6_range(node: Node) -> ParseResult<RangeInclusive<Ipv6Addr>> {
        parse_range!(node, ipv6_lit)
    }

    fn rhs(node: Node) -> ParseResult<ast::Rhs> {
        Ok(match_nodes! {
            node.children();
            [int_lit(i)] => ast::Rhs::Int(i),
            [int_range(r)] => ast::Rhs::IntRange(r),
            [str_lit(s)] => ast::Rhs::String(s),
            [ipv4_lit(i)] => ast::Rhs::Ipv4(i),
            [ipv6_lit(i)] => ast::Rhs::Ipv6(i),
            [ipv4_cidr(c)] => ast::Rhs::Ipv4Cidr(c),
            [ipv6_cidr(c)] => ast::Rhs::Ipv6Cidr(c),
            [ipv4_range(r)] => ast::Rhs::Ipv4Range(r),
            [ipv6_range(r)] => ast::Rhs::Ipv6Range(r)
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
#[allow(clippy::string_lit_as_bytes)]
mod tests {
    use super::*;
    use cidr::Cidr as _;

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
        assert_eq!(parse!(int_lit, "42"), Ok(42));
        assert_eq!(parse!(int_lit, "-42"), Ok(-42));
        assert_eq!(parse!(int_lit, "0x2A"), Ok(42));
        assert_eq!(parse!(int_lit, "-0x2a"), Ok(-42));
        assert_eq!(parse!(int_lit, "052"), Ok(42));
        assert_eq!(parse!(int_lit, "-052"), Ok(-42));
        assert!(parse!(int_lit, "-abc").is_err());
        assert!(parse!(int_lit, "99999999999999999999999999999").is_err());
    }

    #[test]
    fn parse_int_range() {
        assert_eq!(parse!(int_range, "42..0x2b"), Ok(42..=43));
        assert_eq!(parse!(int_range, "-0x2a..0x2A"), Ok(-42..=42));
        assert_eq!(parse!(int_range, "42..42"), Ok(42..=42));
        assert!(parse!(int_range, "42 ..43").is_err());
        assert!(parse!(int_range, "42.. 43").is_err());
        assert!(parse!(int_range, "45..42").is_err());
        assert!(parse!(int_range, "42..z").is_err());
    }

    #[test]
    fn parse_str_lit() {
        assert_eq!(parse!(str_lit, r#""""#), Ok("".as_bytes().into()));

        assert_eq!(
            parse!(str_lit, r#""foobar baz  qux""#),
            Ok("foobar baz  qux".as_bytes().into())
        );

        assert_eq!(
            parse!(str_lit, r#""\n foo \t\r \\ baz \" bar ""#),
            Ok("\n foo \t\r \\ baz \" bar ".as_bytes().into())
        );

        assert_eq!(
            parse!(str_lit, r#""foo \x41\x42 bar\x43""#),
            Ok("foo AB barC".as_bytes().into())
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
        assert_eq!(parse!(bin_op, "bitwise_and"), Ok(ast::BinOp::BitwiseAnd));
        assert_eq!(parse!(bin_op, "contains"), Ok(ast::BinOp::Contains));
        assert_eq!(parse!(bin_op, "~"), Ok(ast::BinOp::Matches));
        assert_eq!(parse!(bin_op, "matches"), Ok(ast::BinOp::Matches));
        assert_eq!(parse!(bin_op, "in"), Ok(ast::BinOp::In));
    }

    #[test]
    fn parse_expr() {
        assert_eq!(
            parse!(expr, "foo.bar.baz"),
            Ok(ast::Expr::Unary(ast::Var("foo.bar.baz".into())))
        );

        assert_eq!(
            parse!(expr, "foo.bar.baz > 42"),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo.bar.baz".into()),
                op: ast::BinOp::Greater,
                rhs: ast::Rhs::Int(42)
            })
        );

        assert_eq!(
            parse!(expr, "foo.bar.baz in 32..42"),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo.bar.baz".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::IntRange(32..=42)
            })
        );

        assert_eq!(
            parse!(expr, "foo == 220.12.13.1"),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::Eq,
                rhs: ast::Rhs::Ipv4(Ipv4Addr::new(220, 12, 13, 1))
            })
        );

        assert_eq!(
            parse!(expr, "foo in 220.12.13.1..220.12.13.2"),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::Ipv4Range(
                    Ipv4Addr::new(220, 12, 13, 1)..=Ipv4Addr::new(220, 12, 13, 2)
                )
            })
        );

        assert_eq!(
            parse!(expr, "foo == 2001:db8::1"),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::Eq,
                rhs: ast::Rhs::Ipv6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1))
            })
        );

        assert_eq!(
            parse!(expr, r#"foo.bar == "test\n""#),
            Ok(ast::Expr::Binary {
                lhs: ast::Var("foo.bar".into()),
                op: ast::BinOp::Eq,
                rhs: ast::Rhs::String("test\n".as_bytes().into())
            })
        );
    }

    #[test]
    fn parse_ipv4_lit() {
        assert_eq!(
            parse!(ipv4_lit, "127.0.0.1"),
            Ok(Ipv4Addr::new(127, 0, 0, 1))
        );

        assert_eq!(
            parse!(ipv4_lit, "192.0.2.235"),
            Ok(Ipv4Addr::new(192, 0, 2, 235))
        );

        assert!(parse!(ipv4_lit, "127.0.0.a").is_err());
    }

    #[test]
    fn parse_ipv6_lit() {
        assert_eq!(
            parse!(ipv6_lit, "::1"),
            Ok(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1))
        );

        assert_eq!(
            parse!(ipv6_lit, "2001:db8::1"),
            Ok(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1))
        );

        assert_eq!(
            parse!(ipv6_lit, "2001:db8::1"),
            Ok(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1))
        );

        assert_eq!(
            parse!(ipv6_lit, "::ffff:255.255.255.255"),
            Ok(Ipv6Addr::new(0, 0, 0, 0, 0, 0xffff, 0xffff, 0xffff))
        );
    }

    #[test]
    fn parse_ipv4_cidr() {
        assert_eq!(
            parse!(ipv4_cidr, "127.0.0.1/32"),
            Ok(Ipv4Cidr::new(Ipv4Addr::new(127, 0, 0, 1), 32).unwrap())
        );

        assert_eq!(
            parse!(ipv4_cidr, "192.0.0.0/16"),
            Ok(Ipv4Cidr::new(Ipv4Addr::new(192, 0, 0, 0), 16).unwrap())
        );

        assert!(parse!(ipv4_cidr, "192.0.0.0/99").is_err());
        assert!(parse!(ipv4_cidr, "192.0.0.1/8").is_err());
    }

    #[test]
    fn parse_ipv4_range() {
        assert_eq!(
            parse!(ipv4_range, "127.0.0.1..127.0.0.128"),
            Ok(Ipv4Addr::new(127, 0, 0, 1)..=Ipv4Addr::new(127, 0, 0, 128))
        );

        assert_eq!(
            parse!(ipv4_range, "192.0.2.235..192.1.2.235"),
            Ok(Ipv4Addr::new(192, 0, 2, 235)..=Ipv4Addr::new(192, 1, 2, 235))
        );

        assert!(parse!(ipv4_range, "192.0.2.235..192.1.2.a").is_err());
        assert!(parse!(ipv4_range, "192.0.2.235..192.0.2.128").is_err());
    }

    #[test]
    fn parse_ipv6_range() {
        assert_eq!(
            parse!(ipv6_range, "::1..::2"),
            Ok(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)..=Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2))
        );

        assert_eq!(
            parse!(ipv6_range, "2001:db8::1..2001:db8::ff"),
            Ok(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1)
                ..=Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 0xff))
        );

        assert!(parse!(ipv6_range, "2001:db8::1..2001:dz8::ff").is_err());
        assert!(parse!(ipv6_range, "2001:db8::ff..2001:db8::11").is_err());
    }
}
