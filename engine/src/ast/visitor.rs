use super::{
    field_expr::{ComparisonExpr, ComparisonOpExpr},
    function_expr::{FunctionCallArgExpr, FunctionCallExpr},
    index_expr::IndexExpr,
    logical_expr::LogicalExpr,
    simple_expr::SimpleExpr,
    Expr, ValueExpr,
};
use crate::scheme::{Field, Function};

/// Trait used to visit all nodes in the AST.
pub trait Visitor<'s>: Sized {
    // `Expr` node visitor methods

    /// Visit [`Expr`] node.
    #[inline(always)]
    fn visit_expr(&mut self, node: &impl Expr<'s>) {
        node.walk(self)
    }

    /// Visit [`SimpleExpr`] node.
    #[inline(always)]
    fn visit_simple_expr(&mut self, node: &SimpleExpr<'s>) {
        self.visit_expr(node)
    }

    /// Visit [`LogicalExpr`] node.
    #[inline(always)]
    fn visit_logical_expr(&mut self, node: &LogicalExpr<'s>) {
        self.visit_expr(node)
    }

    /// Visit [`ComparisonExpr`] node.
    #[inline(always)]
    fn visit_comparison_expr(&mut self, node: &ComparisonExpr<'s>) {
        self.visit_expr(node)
    }

    // `ValueExpr` node visitor methods

    /// Visit [`ValueExpr`] node.
    #[inline(always)]
    fn visit_value_expr(&mut self, node: &impl ValueExpr<'s>) {
        node.walk(self)
    }

    /// Visit [`IndexExpr`] node.
    #[inline(always)]
    fn visit_index_expr(&mut self, node: &IndexExpr<'s>) {
        self.visit_value_expr(node)
    }

    /// Visit [`FunctionCallExpr`] node.
    #[inline(always)]
    fn visit_function_call_expr(&mut self, node: &FunctionCallExpr<'s>) {
        self.visit_value_expr(node)
    }

    /// Visit [`FunctionCallArgExpr`] node.
    #[inline(always)]
    fn visit_function_call_arg_expr(&mut self, node: &FunctionCallArgExpr<'s>) {
        self.visit_value_expr(node)
    }

    // Leaf node visitor methods

    /// Visit [`Field`] node.
    #[inline(always)]
    fn visit_field(&mut self, _: &Field<'s>) {}

    /// Visit [`Function`] node.
    #[inline(always)]
    fn visit_function(&mut self, _: &Function<'s>) {}

    // TODO: add visitor methods for literals?
}

/// Recursively check if a [`Field`] is being used.
pub(crate) struct UsesVisitor<'s> {
    field: Field<'s>,
    uses: bool,
}

impl<'s> UsesVisitor<'s> {
    pub fn new(field: Field<'s>) -> Self {
        Self { field, uses: false }
    }

    pub fn uses(&self) -> bool {
        self.uses
    }
}

impl<'s> Visitor<'s> for UsesVisitor<'s> {
    fn visit_expr(&mut self, node: &impl Expr<'s>) {
        // Stop visiting the AST once we have found one occurence of the field
        if !self.uses {
            node.walk(self)
        }
    }

    fn visit_value_expr(&mut self, node: &impl ValueExpr<'s>) {
        // Stop visiting the AST once we have found one occurence of the field
        if !self.uses {
            node.walk(self)
        }
    }

    fn visit_field(&mut self, f: &Field<'s>) {
        if self.field == *f {
            self.uses = true;
        }
    }
}

/// Recursively check if a [`Field`] is being used in a list comparison.
pub(crate) struct UsesListVisitor<'s> {
    field: Field<'s>,
    uses: bool,
}

impl<'s> UsesListVisitor<'s> {
    pub fn new(field: Field<'s>) -> Self {
        Self { field, uses: false }
    }

    pub fn uses(&self) -> bool {
        self.uses
    }
}

impl<'s> Visitor<'s> for UsesListVisitor<'s> {
    fn visit_expr(&mut self, node: &impl Expr<'s>) {
        // Stop visiting the AST once we have found one occurence of the field
        if !self.uses {
            node.walk(self)
        }
    }

    fn visit_value_expr(&mut self, node: &impl ValueExpr<'s>) {
        // Stop visiting the AST once we have found one occurence of the field
        if !self.uses {
            node.walk(self)
        }
    }

    fn visit_comparison_expr(&mut self, comparison_expr: &ComparisonExpr<'s>) {
        if let ComparisonOpExpr::InList { .. } = comparison_expr.op {
            let mut visitor = UsesVisitor::new(self.field);
            visitor.visit_comparison_expr(comparison_expr);
            if visitor.uses {
                self.uses = true;
            }
        }
        if !self.uses {
            comparison_expr.walk(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        AlwaysList, FunctionArgKind, Identifier, Scheme, SimpleFunctionDefinition,
        SimpleFunctionImpl, SimpleFunctionParam, Type,
    };
    use lazy_static::lazy_static;

    lazy_static! {
        static ref SCHEME: Scheme = {
            let mut scheme = Scheme! {
                http.headers: Map(Bytes),
                http.request.headers.names: Array(Bytes),
                http.request.headers.values: Array(Bytes),
                http.host: Bytes,
                ip.addr: Ip,
                ssl: Bool,
                tcp.port: Int,
            };
            scheme
                .add_function(
                    "echo".into(),
                    SimpleFunctionDefinition {
                        params: vec![SimpleFunctionParam {
                            arg_kind: FunctionArgKind::Field,
                            val_type: Type::Bytes,
                        }],
                        opt_params: vec![],
                        return_type: Type::Bytes,
                        implementation: SimpleFunctionImpl::new(|args| args.next()?.ok()),
                    },
                )
                .unwrap();
            scheme
                .add_list(Type::Bytes, Box::new(AlwaysList::default()))
                .unwrap();
            scheme
        };
    }

    #[test]
    fn test_uses_visitor_simple() {
        let ast = SCHEME.parse(r#"http.host == "test""#).unwrap();
        for (_, identifier) in SCHEME.iter() {
            match identifier {
                Identifier::Field(f) if f.name() == "http.host" => {
                    assert_eq!(ast.uses(f.name()), Ok(true))
                }
                Identifier::Field(f) => assert_eq!(ast.uses(f.name()), Ok(false)),
                Identifier::Function(_) => {}
            }
        }
    }

    #[test]
    fn test_uses_list_visitor_simple() {
        let ast = SCHEME.parse(r#"http.host in $test"#).unwrap();
        for (_, identifier) in SCHEME.iter() {
            match identifier {
                Identifier::Field(f) if f.name() == "http.host" => {
                    assert_eq!(ast.uses_list(f.name()), Ok(true))
                }
                Identifier::Field(f) => assert_eq!(ast.uses_list(f.name()), Ok(false)),
                Identifier::Function(_) => {}
            }
        }
    }

    #[test]
    fn test_uses_visitor_function() {
        let ast = SCHEME.parse(r#"echo(http.host) == "test""#).unwrap();
        for (_, identifier) in SCHEME.iter() {
            match identifier {
                Identifier::Field(f) if f.name() == "http.host" => {
                    assert_eq!(ast.uses(f.name()), Ok(true))
                }
                Identifier::Field(f) => assert_eq!(ast.uses(f.name()), Ok(false)),
                Identifier::Function(_) => {}
            }
        }
    }

    #[test]
    fn test_uses_list_visitor_function() {
        let ast = SCHEME.parse(r#"echo(http.host) in $test"#).unwrap();
        for (_, identifier) in SCHEME.iter() {
            match identifier {
                Identifier::Field(f) if f.name() == "http.host" => {
                    assert_eq!(ast.uses_list(f.name()), Ok(true))
                }
                Identifier::Field(f) => assert_eq!(ast.uses_list(f.name()), Ok(false)),
                Identifier::Function(_) => {}
            }
        }
    }

    #[test]
    fn test_uses_visitor_mapeach() {
        let ast = SCHEME
            .parse(r#"echo(echo(http.headers[*])[*])[0] == "test""#)
            .unwrap();
        for (_, identifier) in SCHEME.iter() {
            match identifier {
                Identifier::Field(f) if f.name() == "http.headers" => {
                    assert_eq!(ast.uses(f.name()), Ok(true))
                }
                Identifier::Field(f) => assert_eq!(ast.uses(f.name()), Ok(false)),
                Identifier::Function(_) => {}
            }
        }
    }

    #[test]
    fn test_uses_list_visitor_mapeach() {
        let ast = SCHEME
            .parse(r#"echo(echo(http.headers[*])[*])[0] in $test"#)
            .unwrap();
        for (_, identifier) in SCHEME.iter() {
            match identifier {
                Identifier::Field(f) if f.name() == "http.headers" => {
                    assert_eq!(ast.uses_list(f.name()), Ok(true))
                }
                Identifier::Field(f) => assert_eq!(ast.uses_list(f.name()), Ok(false)),
                Identifier::Function(_) => {}
            }
        }
    }
}
