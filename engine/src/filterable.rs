use crate::scheme::Scheme;
use crate::{ExecutionContext, LhsValue};
use crate::errors::Error;
use std::net::IpAddr;

pub trait Filterable {
    fn filter_context<'s>(&self, schema: &'s Scheme) -> Result<ExecutionContext<'s>, Error>;
}


pub trait GenContext {
    fn generate_context<'s>(&self, ctx: &mut ExecutionContext<'s>, field_name: &str) -> Result<(), Error>;
}

impl GenContext for String {
    fn generate_context<'s>(&self, ctx: &mut ExecutionContext<'s>, field_name: &str) -> Result<(), Error> {
        println!("gen_ctx String {} {}", field_name, self);
        let value: LhsValue = LhsValue::from(self.to_owned());
        ctx.set_field_value(field_name, value).map_err(Error::TypeMismatchError)?;
        Ok(())
    }
}

impl GenContext for usize {
    fn generate_context<'s>(&self, ctx: &mut ExecutionContext<'s>, field_name: &str) -> Result<(), Error>{
        println!("gen_ctx usize {}", self);
        ctx.set_field_value(field_name, LhsValue::Int(*self as _)).map_err(Error::TypeMismatchError)?;
        Ok(())
    }
}

impl GenContext for IpAddr {
    fn generate_context<'s>(&self, ctx: &mut ExecutionContext<'s>, field_name: &str) -> Result<(), Error> {
        println!("gen_ctx ipaddr {}", self.to_string());
        ctx.set_field_value(field_name, LhsValue::Ip(*self)).map_err(Error::TypeMismatchError)?;
        Ok(())
    }
}

impl<T: GenContext> GenContext for Option<T> {
    fn generate_context<'s>(&self, ctx: &mut ExecutionContext<'s>, field_name: &str) -> Result<(), Error> {
        if let Some(t) = self {
            t.generate_context(ctx, field_name);
        }
        Ok(())
    }
}

