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

    #[inline]
    fn ipv4_range(node: Node) -> ParseResult<RangeInclusive<Ipv4Addr>> {
        parse_range!(node, ipv4_lit)
    }

    #[inline]
    fn ipv6_range(node: Node) -> ParseResult<RangeInclusive<Ipv6Addr>> {
        parse_range!(node, ipv6_lit)
    }

    fn re_lit(node: Node) -> ParseResult<ast::Regex> {
        node.children()
            .single()
            .unwrap()
            .as_str()
            .parse()
            .into_parse_result(&node)
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
            [ipv6_range(r)] => ast::Rhs::Ipv6Range(r),
            [re_lit(r)] => ast::Rhs::Regex(r)
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
    use indoc::indoc;

    macro_rules! parse {
        ($rule:ident, $input:expr) => {
            Parser::parse(Rule::$rule, $input)
                .and_then(|p| p.single())
                .and_then(Parser::$rule)
        };
    }

    macro_rules! ok {
        ($rule:ident $input:expr => $expected:expr) => {
            assert_eq!(parse!($rule, $input), Ok($expected));
        };
    }

    macro_rules! err {
        ($rule:ident $input:expr => $expected:expr) => {
            assert_eq!(
                parse!($rule, $input).unwrap_err().to_string(),
                indoc!($expected)
            );
        };
    }

    #[test]
    fn parse_var() {
        ok! { var "foo" => ast::Var("foo".into()) }
        ok! { var "f1o2o3" => ast::Var("f1o2o3".into()) }
        ok! { var "f1o2o3.bar321" => ast::Var("f1o2o3.bar321".into()) }
        ok! { var "foo.bar.baz" => ast::Var("foo.bar.baz".into()) }

        err! { var "123foo" =>
            " --> 1:1
            |
          1 | 123foo
            | ^---
            |
            = expected var"
        }
    }

    #[test]
    fn parse_int_lit() {
        ok! { int_lit "42" => 42 }
        ok! { int_lit "-42" => -42 }
        ok! { int_lit "0x2A" => 42 }
        ok! { int_lit "-0x2a" => -42 }
        ok! { int_lit "052" => 42 }
        ok! { int_lit "-052" => -42 }

        err! { int_lit "-abc" =>
            " --> 1:2
            |
          1 | -abc
            |  ^---
            |
            = expected oct_digits or dec_digits"
        }

        err! { int_lit "99999999999999999999999999999" =>
            " --> 1:1
            |
          1 | 99999999999999999999999999999
            | ^---------------------------^
            |
            = number too large to fit in target type"
        }
    }

    #[test]
    fn parse_int_range() {
        ok! { int_range "42..0x2b" => 42..=43 }
        ok! { int_range "-0x2a..0x2A" => -42..=42 }
        ok! { int_range "42..42" => 42..=42 }

        err! { int_range "42.. 43" =>
            " --> 1:5
            |
          1 | 42.. 43
            |     ^---
            |
            = expected int_lit"
        }

        err! { int_range "45..42" =>
            " --> 1:1
            |
          1 | 45..42
            | ^----^
            |
            = start of the range is greater than the end"
        }

        err! { int_range "42..z" =>
            " --> 1:5
            |
          1 | 42..z
            |     ^---
            |
            = expected int_lit"
        }
    }

    #[test]
    fn parse_str_lit() {
        ok! { str_lit r#""""# => "".as_bytes().into() }
        ok! { str_lit r#""foobar baz  qux""# => "foobar baz  qux".as_bytes().into() }
        ok! { str_lit r#""foo \x41\x42 bar\x43""# => "foo AB barC".as_bytes().into() }

        ok! {
            str_lit r#""\n foo \t\r \\ baz \" bar ""#  =>
            "\n foo \t\r \\ baz \" bar ".as_bytes().into()
        }

        err! { str_lit r#""foobar \i""# =>
            r#" --> 1:10
            |
          1 | "foobar \i"
            |          ^---
            |
            = expected esc_alias"#
        }

        err! { str_lit r#""foobar \x3z""# =>
            r#" --> 1:11
            |
          1 | "foobar \x3z"
            |           ^---
            |
            = expected esc_hex_byte"#
        }
    }

    #[test]
    fn parse_bin_op() {
        ok! { bin_op "==" => ast::BinOp::Eq }
        ok! { bin_op "eq" => ast::BinOp::Eq }
        ok! { bin_op "!=" => ast::BinOp::NotEq }
        ok! { bin_op "ne" => ast::BinOp::NotEq }
        ok! { bin_op ">=" => ast::BinOp::GreaterOrEq }
        ok! { bin_op "ge" => ast::BinOp::GreaterOrEq }
        ok! { bin_op "<=" => ast::BinOp::LessOrEq }
        ok! { bin_op "le" => ast::BinOp::LessOrEq }
        ok! { bin_op ">" => ast::BinOp::Greater }
        ok! { bin_op "gt" => ast::BinOp::Greater }
        ok! { bin_op "<" => ast::BinOp::Less }
        ok! { bin_op "lt" => ast::BinOp::Less }
        ok! { bin_op "&" => ast::BinOp::BitwiseAnd }
        ok! { bin_op "bitwise_and" => ast::BinOp::BitwiseAnd }
        ok! { bin_op "contains" => ast::BinOp::Contains }
        ok! { bin_op "~" => ast::BinOp::Matches }
        ok! { bin_op "matches" => ast::BinOp::Matches }
        ok! { bin_op "in" => ast::BinOp::In }
    }

    #[test]
    fn pare_expr() {
        ok! { expr "foo.bar.baz" => ast::Expr::Unary(ast::Var("foo.bar.baz".into())) }

        ok! {
            expr "foo.bar.baz > 42" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo.bar.baz".into()),
                op: ast::BinOp::Greater,
                rhs: ast::Rhs::Int(42)
            }
        }

        ok! {
            expr "foo.bar.baz in 32..42" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo.bar.baz".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::IntRange(32..=42)
            }
        }

        ok! {
            expr "foo == 220.12.13.1" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::Eq,
                rhs: ast::Rhs::Ipv4(Ipv4Addr::new(220, 12, 13, 1))
            }
        }

        ok! {
            expr "foo in 220.12.13.1..220.12.13.2" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::Ipv4Range(
                    Ipv4Addr::new(220, 12, 13, 1)..=Ipv4Addr::new(220, 12, 13, 2)
                )
            }
        }

        ok! {
            expr "foo in 192.0.0.0/16" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::Ipv4Cidr(
                    Ipv4Cidr::new(Ipv4Addr::new(192, 0, 0, 0), 16).unwrap()
                )
            }
        }

        ok! {
            expr "foo in ::1/128" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::In,
                rhs: ast::Rhs::Ipv6Cidr(
                    Ipv6Cidr::new(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1), 128).unwrap()
                )
            }
        }

        ok! {
            expr "foo == 2001:db8::1" =>
            ast::Expr::Binary {
                lhs: ast::Var("foo".into()),
                op: ast::BinOp::Eq,
                rhs: ast::Rhs::Ipv6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1))
            }
        }

        ok! {
            expr r#"foo.bar == "test\n""# =>
            ast::Expr::Binary {
                lhs: ast::Var("foo.bar".into()),
                op: ast::BinOp::Eq,
                rhs: ast::Rhs::String("test\n".as_bytes().into())
            }
        }
    }

    #[test]
    fn parse_ipv4_lit() {
        ok! { ipv4_lit "127.0.0.1" => Ipv4Addr::new(127, 0, 0, 1) }
        ok! { ipv4_lit "192.0.2.235" => Ipv4Addr::new(192, 0, 2, 235) }

        err! { ipv4_lit "127.0.0.a" =>
            " --> 1:1
            |
          1 | 127.0.0.a
            | ^---
            |
            = expected ipv4_lit"
        }

        err! { ipv4_lit "300.0.0.1" =>
            " --> 1:1
            |
          1 | 300.0.0.1
            | ^-------^
            |
            = invalid IP address syntax"
        }
    }

    #[test]
    fn parse_ipv6_lit() {
        ok! { ipv6_lit "::" => Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0) }
        ok! { ipv6_lit "::1" => Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1) }
        ok! { ipv6_lit "2001:db8::1" => Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1) }
        ok! { ipv6_lit "2001:db8::1" => Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1) }

        ok! {
            ipv6_lit "::ffff:255.255.255.255" =>
            Ipv6Addr::new(0, 0, 0, 0, 0, 0xffff, 0xffff, 0xffff)
        }

        err! { ipv6_lit "2001:dz8::1" =>
            " --> 1:1
            |
          1 | 2001:dz8::1
            | ^---------^
            |
            = invalid IP address syntax"
        }
    }

    #[test]
    fn parse_ipv4_cidr() {
        ok! {
            ipv4_cidr "127.0.0.1/32" =>
            Ipv4Cidr::new(Ipv4Addr::new(127, 0, 0, 1), 32).unwrap()
        }

        ok! {
            ipv4_cidr "192.0.0.0/16" =>
            Ipv4Cidr::new(Ipv4Addr::new(192, 0, 0, 0), 16).unwrap()
        }

        err! { ipv4_cidr "192.0.0.0/99" =>
            " --> 1:1
            |
          1 | 192.0.0.0/99
            | ^----------^
            |
            = invalid length for network: Network length 99 is too long for Ipv4 (maximum: 32)"
        }

        err! { ipv4_cidr "192.0.0.1/8" =>
            " --> 1:1
            |
          1 | 192.0.0.1/8
            | ^---------^
            |
            = host part of address was not zero"
        }
    }

    #[test]
    fn parse_ipv6_cidr() {
        ok! {
            ipv6_cidr "::1/128" =>
            Ipv6Cidr::new(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1), 128).unwrap()
        }

        ok! {
            ipv6_cidr "::/10" =>
            Ipv6Cidr::new(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 0), 10).unwrap()
        }

        err! { ipv6_cidr "::1/560" =>
            " --> 1:1
            |
          1 | ::1/560
            | ^-----^
            |
            = couldn't parse length in network: number too large to fit in target type"
        }
    }

    #[test]
    fn parse_ipv4_range() {
        ok! {
            ipv4_range "127.0.0.1..127.0.0.128" =>
            Ipv4Addr::new(127, 0, 0, 1)..=Ipv4Addr::new(127, 0, 0, 128)
        }

        ok! {
            ipv4_range "192.0.2.235..192.1.2.235" =>
            Ipv4Addr::new(192, 0, 2, 235)..=Ipv4Addr::new(192, 1, 2, 235)
        }

        err! { ipv4_range "192.0.2.235..192.1.2.a" =>
            " --> 1:14
            |
          1 | 192.0.2.235..192.1.2.a
            |              ^---
            |
            = expected ipv4_lit"
        }

        err! { ipv4_range "192.0.2.235..192.0.2.128" =>
            " --> 1:1
            |
          1 | 192.0.2.235..192.0.2.128
            | ^----------------------^
            |
            = start of the range is greater than the end"
        }
    }

    #[test]
    fn parse_ipv6_range() {
        ok! {
            ipv6_range "::1..::2" =>
            Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1)..=Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 2)
        }

        ok! {
            ipv6_range "2001:db8::1..2001:db8::ff" =>
            Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1)
                ..=Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 0xff)
        }

        err! { ipv6_range "2001:db8::1..2001:dz8::ff" =>
            " --> 1:14
            |
          1 | 2001:db8::1..2001:dz8::ff
            |              ^----------^
            |
            = invalid IP address syntax"
        }

        err! { ipv6_range "2001:db8::ff..2001:db8::11" =>
            " --> 1:1
            |
          1 | 2001:db8::ff..2001:db8::11
            | ^------------------------^
            |
            = start of the range is greater than the end"
        }
    }

    #[test]
    fn parse_re_lit() {
        ok! {
            re_lit r#"/[-]?[0-9]+[,.]?[0-9]*([/][0-9]+[,.]?[0-9]*)*/"# =>
            r#"[-]?[0-9]+[,.]?[0-9]*([/][0-9]+[,.]?[0-9]*)*"#.parse().unwrap()
        }
    }
}
