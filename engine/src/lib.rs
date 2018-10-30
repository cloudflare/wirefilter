#[macro_use]
extern crate failure;

#[macro_use]
extern crate serde;

#[cfg(test)]
#[macro_use]
extern crate serde_json;

#[cfg(test)]
#[macro_use]
extern crate indoc;

#[cfg(test)]
#[macro_use]
extern crate lazy_static;

extern crate cidr;
extern crate fnv;
extern crate indexmap;
extern crate memmem;
extern crate regex;

#[macro_use]
mod lex;

mod ast;
mod execution_context;
mod range_set;
mod rhs_types;
mod scheme;
mod strict_partial_ord;
mod types;
mod vec_set;

pub use self::{
    ast::Filter,
    execution_context::ExecutionContext,
    scheme::{ParseError, Scheme},
    types::{GetType, LhsValue, Type},
};
