use crate::scheme::Scheme;
use crate::ExecutionContext;
use crate::errors::Error;


pub trait Filterable {
    fn filter_context<'s>(&self, schema: &'s Scheme) -> Result<ExecutionContext<'s>, Error>;
}
