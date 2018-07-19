use super::{simple::SimpleExpr, Expr};
use execution_context::ExecutionContext;
use lex::{Lex, LexResult};
use scheme::{FieldIndex, Scheme};

lex_enum!(#[derive(PartialOrd, Ord)] CombiningOp {
    "or" | "||" => Or,
    "xor" | "^^" => Xor,
    "and" | "&&" => And,
});

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum CombinedExpr<'s> {
    Simple(SimpleExpr<'s>),
    Combining {
        op: CombiningOp,
        items: Vec<CombinedExpr<'s>>,
    },
}

impl<'s> CombinedExpr<'s> {
    fn lex_combining_op(input: &str) -> (Option<CombiningOp>, &str) {
        match CombiningOp::lex(input.trim_left()) {
            Ok((op, input)) => (Some(op), input.trim_left()),
            Err(_) => (None, input),
        }
    }

    fn lex_more_with_precedence<'i>(
        self,
        scheme: &'s Scheme,
        min_prec: Option<CombiningOp>,
        mut lookahead: (Option<CombiningOp>, &'i str),
    ) -> LexResult<'i, Self> {
        let mut lhs = self;

        while let Some(op) = lookahead.0 {
            let mut rhs = SimpleExpr::lex(scheme, lookahead.1)
                .map(|(op, input)| ((CombinedExpr::Simple(op), input)))?;

            loop {
                lookahead = Self::lex_combining_op(rhs.1);
                if lookahead.0 <= Some(op) {
                    break;
                }
                rhs = rhs
                    .0
                    .lex_more_with_precedence(scheme, lookahead.0, lookahead)?;
            }

            match lhs {
                CombinedExpr::Combining {
                    op: lhs_op,
                    ref mut items,
                }
                    if lhs_op == op =>
                {
                    items.push(rhs.0);
                }
                _ => {
                    lhs = CombinedExpr::Combining {
                        op: op,
                        items: vec![lhs, rhs.0],
                    };
                }
            }

            if lookahead.0 < min_prec {
                // pretend we haven't seen an operator if its precedence is
                // outside of our limits
                lookahead = (None, rhs.1);
            }
        }

        Ok((lhs, lookahead.1))
    }
}

impl<'s> Expr<'s> for CombinedExpr<'s> {
    fn uses(&self, field: FieldIndex<'s>) -> bool {
        match self {
            CombinedExpr::Simple(op) => op.uses(field),
            CombinedExpr::Combining { items, .. } => items.iter().any(|op| op.uses(field)),
        }
    }

    fn lex<'i>(scheme: &'s Scheme, input: &'i str) -> LexResult<'i, Self> {
        let (lhs, input) = SimpleExpr::lex(scheme, input)?;
        let lookahead = Self::lex_combining_op(input);
        CombinedExpr::Simple(lhs).lex_more_with_precedence(scheme, None, lookahead)
    }

    fn execute(&self, ctx: &ExecutionContext<'s>) -> bool {
        match self {
            CombinedExpr::Simple(op) => op.execute(ctx),
            CombinedExpr::Combining { op, items } => {
                let mut results = items.iter().map(|op| op.execute(ctx));
                match op {
                    CombiningOp::And => results.all(|res| res),
                    CombiningOp::Or => results.any(|res| res),
                    CombiningOp::Xor => results.fold(false, |acc, res| acc ^ res),
                }
            }
        }
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use types::Type;

//     use cidr::{Cidr, IpCidr, Ipv4Cidr, Ipv6Cidr};
//     use std::net::{Ipv4Addr, Ipv6Addr};

//     #[test]
//     fn parse() {
//         let scheme: Scheme = [
//             ("http.host", Type::Bytes),
//             ("port", Type::Unsigned),
//             ("ip.src", Type::Ip),
//             ("isTCP", Type::Bool),
//         ].iter()
//             .map(|&(k, t)| (k.to_owned(), t))
//             .collect();

//         let http_host_field = scheme.get_field_index("http.host").unwrap();

//         assert_ok!(
//             CombinedExpr::lex(
//                 &scheme,
//                 r#"http.host contains "t" or http.host contains E0:BE or http.host matches "^\d+""#
//             ),
//             CombinedExpr::Combining {
//                 op: CombiningOp::Or,
//                 items: [
//                     r"(?u)t",
//                     r"\xE0\xBE",
//                     r"^\d+",
//                 ].map(|re| CombinedExpr::Simple(UnaryExpr {
//                     not_depth: 0,
//                     base: SimpleExpr::Field(FieldExpr {
//                         field: http_host_field.clone(),
//                         op: FieldOp::Matches(Regex::new(re).unwrap())
//                     })
//                 })).collect()
//             }
//         );
//         assert_ok!(
//             context.parse("port in { 80 443 }"),
//             Ok(Filter::Op(
//                 FilterField {
//                     field: Field::new("port"),
//                     index: 1
//                 },
//                 FilterExpr::OneOf(RhsValues::Unsigned(vec![80, 443]))
//             ))
//         );
//         assert_eq!(
//             context.parse(
//                 "not ip.src in { 127.0.0.0/8 ::1/128 } and (port == 80) and !isTCP or port >= 1024"
//             ),
//             Ok(CombinedExpr::Combining(
//                 CombiningOp::Or,
//                 vec![
//                     CombinedExpr::Combining(
//                         CombiningOp::And,
//                         vec![
//                             Filter::Simple(
//                                 UnaryExpr::Not,
//                                 Box::new(Filter::Op(
//                                     FilterField {
//                                         field: Field::new("ip.src"),
//                                         index: 2,
//                                     },
//                                     FilterExpr::OneOf(RhsValues::Ip(vec![
//                                         IpCidr::V4(
//                                             Ipv4Cidr::new(Ipv4Addr::new(127, 0, 0, 0), 8).unwrap(),
//                                         ).into(),
//                                         IpCidr::V6(Ipv6Cidr::new(Ipv6Addr::from(1), 128).unwrap())
//                                             .into(),
//                                     ])),
//                                 )),
//                             ),
//                             Filter::Op(
//                                 FilterField {
//                                     field: Field::new("port"),
//                                     index: 1,
//                                 },
//                                 FilterExpr::Ordering(OrderingOp::Equal, RhsValue::Unsigned(80)),
//                             ),
//                             Filter::Simple(
//                                 UnaryExpr::Not,
//                                 Box::new(Filter::Op(
//                                     FilterField {
//                                         field: Field::new("isTCP"),
//                                         index: 3,
//                                     },
//                                     FilterExpr::Ordering(OrderingOp::Equal, RhsValue::Bool(true)),
//                                 )),
//                             ),
//                         ],
//                     ),
//                     Filter::Op(
//                         FilterField {
//                             field: Field::new("port"),
//                             index: 1,
//                         },
//                         FilterExpr::Ordering(OrderingOp::GreaterThanEqual, RhsValue::Unsigned(1024)),
//                     ),
//                 ]
//             ))
//         );
//     }
// }
