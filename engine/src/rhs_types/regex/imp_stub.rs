use crate::{FilterParser, RegexFormat};
use thiserror::Error;

pub(crate) struct StubRegex {}

impl Regex for StubRegex {
    /// Not implemented and will panic if called.
    fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }
}

/// Default regex provider.
#[derive(Debug, Default)]
pub struct DefaultRegexProvider;

impl RegexProvider for DefaultRegexProvider {
    fn lookup(&self, pattern: &str) -> Result<Arc<dyn AsRegex>, Error> {
        Ok(Arc::new(StubRegex {}))
    }
}
