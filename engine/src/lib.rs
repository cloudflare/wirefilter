//! This is the main crate for the filter engine.
//!
//! It contains public APIs for parsing filter syntax, compiling them into
//! an executable IR and, finally, executing filters against provided values.
//!
//! # Example
//!
//! ```
//! use wirefilter::{ExecutionContext, Scheme, Type};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // Create a map of possible filter fields.
//!     let scheme = Scheme! {
//!         http.method: Bytes,
//!         http.ua: Bytes,
//!         port: Int,
//!     };
//!
//!     // Parse a Wireshark-like expression into an AST.
//!     let ast = scheme.parse(
//!         r#"
//!             http.method != "POST" &&
//!             not http.ua matches "(googlebot|facebook)" &&
//!             port in {80 443}
//!         "#,
//!     )?;
//!
//!     println!("Parsed filter representation: {:?}", ast);
//!
//!     // Compile the AST into an executable filter.
//!     let filter = ast.compile();
//!
//!     // Set runtime field values to test the filter against.
//!     let mut ctx = ExecutionContext::new(&scheme);
//!
//!     ctx.set_field_value(scheme.get_field("http.method").unwrap(), "GET")?;
//!
//!     ctx.set_field_value(
//!         scheme.get_field("http.ua").unwrap(),
//!         "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:66.0) Gecko/20100101 Firefox/66.0",
//!     )?;
//!
//!     ctx.set_field_value(scheme.get_field("port").unwrap(), 443)?;
//!
//!     // Execute the filter with given runtime values.
//!     println!("Filter matches: {:?}", filter.execute(&ctx)?); // true
//!
//!     // Amend one of the runtime values and execute the filter again.
//!     ctx.set_field_value(scheme.get_field("port").unwrap(), 8080)?;
//!
//!     println!("Filter matches: {:?}", filter.execute(&ctx)?); // false
//!
//!     Ok(())
//! }
//! ```
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

#[macro_use]
mod lex;

#[macro_use]
mod scheme;

mod ast;
mod compiler;
mod execution_context;
mod filter;
mod functions;
mod lhs_types;
mod list_matcher;
mod range_set;
mod rhs_types;
mod searcher;
mod strict_partial_ord;
pub mod types;

pub use self::{
    ast::{
        field_expr::{ComparisonExpr, ComparisonOpExpr, OrderingOp},
        function_expr::{FunctionCallArgExpr, FunctionCallExpr},
        index_expr::IndexExpr,
        logical_expr::{LogicalExpr, LogicalOp},
        simple_expr::SimpleExpr,
        visitor::{Visitor, VisitorMut},
        Expr, FilterAst, ValueExpr,
    },
    compiler::{Compiler, DefaultCompiler},
    execution_context::{ExecutionContext, InvalidListMatcherError},
    filter::{CompiledExpr, CompiledOneExpr, CompiledValueExpr, CompiledVecExpr, Filter},
    functions::{
        FunctionArgInvalidConstantError, FunctionArgKind, FunctionArgKindMismatchError,
        FunctionArgs, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
        FunctionParamError, SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionOptParam,
        SimpleFunctionParam,
    },
    lex::LexErrorKind,
    lhs_types::{Array, Map},
    list_matcher::{
        AlwaysList, AlwaysListMatcher, ListDefinition, ListMatcher, ListMatcherWrapper, NeverList,
        NeverListMatcher,
    },
    rhs_types::{Bytes, Regex, RegexError},
    scheme::{
        Field, FieldIndex, FieldRedefinitionError, Function, FunctionRedefinitionError, Identifier,
        IdentifierRedefinitionError, List, ParseError, Scheme, SchemeMismatchError,
        UnknownFieldError,
    },
    types::{ExpectedType, GetType, LhsValue, RhsValue, RhsValues, Type, TypeMismatchError},
};
