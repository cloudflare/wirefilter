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
//!     ctx.set_field_value("http.method", "GET")?;
//!
//!     ctx.set_field_value(
//!         "http.ua",
//!         "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:66.0) Gecko/20100101 Firefox/66.0",
//!     )?;
//!
//!     ctx.set_field_value("port", 443)?;
//!
//!     // Execute the filter with given runtime values.
//!     println!("Filter matches: {:?}", filter.execute(&ctx)?); // true
//!
//!     // Amend one of the runtime values and execute the filter again.
//!     ctx.set_field_value("port", 8080)?;
//!
//!     println!("Filter matches: {:?}", filter.execute(&ctx)?); // false
//!
//!     Ok(())
//! }
//! ```
#![warn(missing_docs)]

extern crate cfg_if;
extern crate failure;
extern crate serde;

#[cfg(test)]
extern crate indoc;

#[cfg(test)]
extern crate lazy_static;

#[cfg(test)]
extern crate serde_json;

extern crate cidr;
extern crate fnv;
extern crate indexmap;
extern crate memmem;

#[cfg(feature = "regex")]
extern crate regex;

#[macro_use]
mod lex;

#[macro_use]
mod scheme;

mod ast;
mod execution_context;
mod filter;
mod heap_searcher;
mod range_set;
mod rhs_types;
mod strict_partial_ord;
mod types;

pub use self::{
    ast::FilterAst,
    execution_context::{ExecutionContext, FieldValueTypeMismatchError},
    filter::{Filter, SchemeMismatchError},
    scheme::{FieldRedefinitionError, ParseError, Scheme, UnknownFieldError},
    types::{GetType, LhsValue, Type},
};
