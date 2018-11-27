#[derive(Clone)]
pub struct Regex(::regex::bytes::Regex);

pub type Error = ::regex::Error;

impl Regex {
    pub fn new(s: &str) -> Result<Self, Error> {
        ::regex::bytes::RegexBuilder::new(s)
            .unicode(false)
            .build()
            .map(Regex)
    }

    pub fn is_match(&self, text: &[u8]) -> bool {
        self.0.is_match(text)
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}
