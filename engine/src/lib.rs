//! This is the main crate for the filter engine.
//!
//! It contains public APIs for parsing filter syntax, compiling them into
//! an executable IR and, finally, executing filters against provided values.

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

mod ast;
mod execution_context;
mod heap_searcher;
mod range_set;
mod rhs_types;
mod scheme;
mod strict_partial_ord;
mod types;
mod compiled_expr;

pub use self::{
    ast::Filter,
    execution_context::ExecutionContext,
    scheme::{ParseError, Scheme},
    types::{GetType, LhsValue, Type},
    compiled_expr::CompiledExpr
};
