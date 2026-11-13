use super::Error;
use crate::{ParserSettings, RegexFormat};
use arcstr::ArcStr;

/// Dummy regex wrapper that can only store a pattern
/// but not actually be used for matching.
#[derive(Clone)]
pub struct Regex {
    pattern: ArcStr,
    format: RegexFormat,
}

pub(crate) struct CompiledRegex;

impl CompiledRegex {
    pub(super) fn is_match(&self, _input: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }
}

impl Regex {
    pub(crate) fn into_compiled(self) -> CompiledRegex {
        CompiledRegex
    }

    /// Creates a new dummy regex.
    pub fn new(
        pattern: impl Into<ArcStr>,
        format: RegexFormat,
        _: &ParserSettings,
    ) -> Result<Self, Error> {
        Ok(Self {
            pattern: pattern.into(),
            format,
        })
    }

    /// Not implemented and will panic if called.
    pub fn is_match(&self, _text: &[u8]) -> bool {
        unimplemented!("Engine was built without regex support")
    }

    /// Returns the original string of this dummy regex wrapper.
    pub fn as_str(&self) -> &str {
        &self.pattern
    }

    /// Returns the shared pattern of this dummy regex wrapper.
    #[inline]
    pub fn pattern(&self) -> &ArcStr {
        &self.pattern
    }

    /// Returns the format behind the regex
    pub fn format(&self) -> RegexFormat {
        self.format
    }
}
