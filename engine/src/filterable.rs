use crate::scheme::Scheme;
use crate::{ExecutionContext, LhsValue};
use crate::errors::Error;
use std::net::IpAddr;

pub trait Filterable {
    fn filter_context<'s>(&self, schema: &'s Scheme) -> Result<ExecutionContext<'s>, Error>;
}


pub trait GenContext<T> {
    fn generate_context<'s>(&self, schema: &'s Scheme, field_name: &str) -> Result<ExecutionContext<'s>, Error>;
}

impl GenContext<String> for String {
    fn generate_context<'s>(&self, schema: &'s Scheme, field_name: &str) -> Result<ExecutionContext<'s>, Error> {
        println!("gen_ctx String {} {}", field_name, self);
        unimplemented!()
    }
}

impl GenContext<usize> for usize {
    fn generate_context<'s>(&self, schema: &'s Scheme, field_name: &str) -> Result<ExecutionContext<'s>, Error> {
        println!("gen_ctx usize {}", self);
        unimplemented!()
    }
}

impl GenContext<IpAddr> for IpAddr {
    fn generate_context<'s>(&self, schema: &'s Scheme, field_name: &str) -> Result<ExecutionContext<'s>, Error> {
        println!("gen_ctx ipaddr {}", self.to_string());
        unimplemented!()
    }
}

