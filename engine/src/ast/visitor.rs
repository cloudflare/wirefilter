use super::{
    field_expr::{ComparisonExpr, ComparisonOpExpr},
    function_expr::{FunctionCallArgExpr, FunctionCallExpr},
    index_expr::IndexExpr,
    logical_expr::LogicalExpr,
    Expr, ValueExpr,
};
use crate::scheme::{Field, Function};

/// Trait used to immutably visit all nodes in the AST.
pub trait Visitor<'s, 'a>: Sized {
    // `Expr` node visitor methods

    /// Visit [`Expr`] node.
    #[inline]
    fn visit_expr(&mut self, node: &'a impl Expr<'s>) {
        node.walk(self)
    }

    /// Visit [`LogicalExpr`] node.
    #[inline]
    fn visit_logical_expr(&mut self, node: &'a LogicalExpr<'s>) {
        self.visit_expr(node)
    }

    /// Visit [`ComparisonExpr`] node.
    #[inline]
    fn visit_comparison_expr(&mut self, node: &'a ComparisonExpr<'s>) {
        self.visit_expr(node)
    }

    // `ValueExpr` node visitor methods

    /// Visit [`ValueExpr`] node.
    #[inline]
    fn visit_value_expr(&mut self, node: &'a impl ValueExpr<'s>) {
        node.walk(self)
    }

    /// Visit [`IndexExpr`] node.
    #[inline]
    fn visit_index_expr(&mut self, node: &'a IndexExpr<'s>) {
        self.visit_value_expr(node)
    }

    /// Visit [`FunctionCallExpr`] node.
    #[inline]
    fn visit_function_call_expr(&mut self, node: &'a FunctionCallExpr<'s>) {
        self.visit_value_expr(node)
    }

    /// Visit [`FunctionCallArgExpr`] node.
    #[inline]
    fn visit_function_call_arg_expr(&mut self, node: &'a FunctionCallArgExpr<'s>) {
        self.visit_value_expr(node)
    }

    // Leaf node visitor methods

    /// Visit [`Field`] node.
    #[inline]
    fn visit_field(&mut self, _: &'a Field<'s>) {}

    /// Visit [`Function`] node.
    #[inline]
    fn visit_function(&mut self, _: &'a Function<'s>) {}

    // TODO: add visitor methods for literals?
}

/// Trait used to mutably visit all nodes in the AST.
///
/// Note that this trait is dangerous and any modification
/// to the AST should be done with cautions and respect
/// some invariants such as keeping type coherency.
pub trait VisitorMut<'s, 'a>: Sized {
    // `Expr` node visitor methods

    /// Visit [`Expr`] node.
    #[inline]
    fn visit_expr(&mut self, node: &'a mut impl Expr<'s>) {
        node.walk_mut(self)
    }

    /// Visit [`LogicalExpr`] node.
    #[inline]
    fn visit_logical_expr(&mut self, node: &'a mut LogicalExpr<'s>) {
        self.visit_expr(node)
    }

    /// Visit [`ComparisonExpr`] node.
    #[inline]
    fn visit_comparison_expr(&mut self, node: &'a mut ComparisonExpr<'s>) {
        self.visit_expr(node)
    }

    // `ValueExpr` node visitor methods

    /// Visit [`ValueExpr`] node.
    #[inline]
    fn visit_value_expr(&mut self, node: &'a mut impl ValueExpr<'s>) {
        node.walk_mut(self)
    }

    /// Visit [`IndexExpr`] node.
    #[inline]
    fn visit_index_expr(&mut self, node: &'a mut IndexExpr<'s>) {
        self.visit_value_expr(node)
    }

    /// Visit [`FunctionCallExpr`] node.
    #[inline]
    fn visit_function_call_expr(&mut self, node: &'a mut FunctionCallExpr<'s>) {
        self.visit_value_expr(node)
    }

    /// Visit [`FunctionCallArgExpr`] node.
    #[inline]
    fn visit_function_call_arg_expr(&mut self, node: &'a mut FunctionCallArgExpr<'s>) {
        self.visit_value_expr(node)
    }

    // Leaf node visitor methods

    /// Visit [`Field`] node.
    #[inline]
    fn visit_field(&mut self, _: &'a Field<'s>) {}

    /// Visit [`Function`] node.
    #[inline]
    fn visit_function(&mut self, _: &'a Function<'s>) {}

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

impl<'s> Visitor<'s, '_> for UsesVisitor<'s> {
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

impl<'s> Visitor<'s, '_> for UsesListVisitor<'s> {
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
        AlwaysList, FunctionArgKind, Scheme, SimpleFunctionDefinition, SimpleFunctionImpl,
        SimpleFunctionParam, Type,
    };
    use std::sync::LazyLock;

    static SCHEME: LazyLock<Scheme> = LazyLock::new(|| {
        let mut builder = Scheme! {
            http.headers: Map(Bytes),
            http.request.headers.names: Array(Bytes),
            http.request.headers.values: Array(Bytes),
            http.host: Bytes,
            ip.addr: Ip,
            ssl: Bool,
            tcp.port: Int,
        };
        builder
            .add_function(
                "echo",
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
        builder
            .add_list(Type::Bytes, Box::new(AlwaysList {}))
            .unwrap();
        builder.build()
    });

    #[test]
    fn test_uses_visitor_simple() {
        let ast = SCHEME.parse(r#"http.host == "test""#).unwrap();
        for field in SCHEME.fields() {
            assert_eq!(ast.uses(field.name()), Ok(field.name() == "http.host"));
        }
    }

    #[test]
    fn test_uses_list_visitor_simple() {
        let ast = SCHEME.parse(r#"http.host in $test"#).unwrap();
        for field in SCHEME.fields() {
            assert_eq!(ast.uses(field.name()), Ok(field.name() == "http.host"));
        }
    }

    #[test]
    fn test_uses_visitor_function() {
        let ast = SCHEME.parse(r#"echo(http.host) == "test""#).unwrap();
        for field in SCHEME.fields() {
            assert_eq!(ast.uses(field.name()), Ok(field.name() == "http.host"));
        }
    }

    #[test]
    fn test_uses_list_visitor_function() {
        let ast = SCHEME.parse(r#"echo(http.host) in $test"#).unwrap();
        for field in SCHEME.fields() {
            assert_eq!(ast.uses(field.name()), Ok(field.name() == "http.host"));
        }
    }

    #[test]
    fn test_uses_visitor_mapeach() {
        let ast = SCHEME
            .parse(r#"echo(echo(http.headers[*])[*])[0] == "test""#)
            .unwrap();
        for field in SCHEME.fields() {
            assert_eq!(ast.uses(field.name()), Ok(field.name() == "http.headers"));
        }
    }

    #[test]
    fn test_uses_list_visitor_mapeach() {
        let ast = SCHEME
            .parse(r#"echo(echo(http.headers[*])[*])[0] in $test"#)
            .unwrap();
        for field in SCHEME.fields() {
            assert_eq!(ast.uses(field.name()), Ok(field.name() == "http.headers"));
        }
    }
}
