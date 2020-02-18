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
//! fn main() -> Result<(), failure::Error> {
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

#[macro_use]
mod lex;

#[macro_use]
mod scheme;

mod ast;
mod execution_context;
mod filter;
mod functions;
mod heap_searcher;
mod range_set;
mod rhs_types;
mod strict_partial_ord;
mod types;

pub use self::{
    ast::FilterAst,
    execution_context::ExecutionContext,
    filter::Filter,
    functions::{
        FunctionArgInvalidConstantError, FunctionArgKind, FunctionArgKindMismatchError,
        FunctionArgs, FunctionDefinition, FunctionDefinitionContext, FunctionParam,
        FunctionParamError, SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionOptParam,
        SimpleFunctionParam,
    },
    lex::LexErrorKind,
    scheme::{
        Field, FieldIndex, FieldRedefinitionError, ItemRedefinitionError, ParseError, Scheme,
        SchemeMismatchError, UnknownFieldError,
    },
    types::{Array, ExpectedType, GetType, LhsValue, Map, Type, TypeMismatchError},
};
