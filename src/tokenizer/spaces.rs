use tokenizer::{Lex, LexResult};
use tokenizer::utils::take_while;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spaces;

impl<'a> Lex<'a> for Spaces {
    fn lex(input: &str) -> LexResult<Self> {
        take_while(input, "whitespace", char::is_whitespace).map(|(_, rest)| (Spaces, rest))
    }
}
