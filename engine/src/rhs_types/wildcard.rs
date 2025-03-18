use crate::lex::{LexResult, LexWith};
use crate::rhs_types::bytes::lex_quoted_or_raw_string;
use crate::{Bytes, FilterParser, LexErrorKind};
use serde::{Serialize, Serializer};
use std::{
    fmt::{self, Debug, Formatter},
    hash::{Hash, Hasher},
};
use thiserror::Error;
use wildcard::WildcardToken;

#[derive(Eq, PartialEq, Error, Debug)]
pub enum WildcardError {
    #[error("invalid wildcard: {0}")]
    InvalidWildcard(
        #[source]
        #[from]
        wildcard::WildcardError,
    ),

    #[error("wildcard has {count} star metacharacters, but the limit is {limit}")]
    TooManyStarMetacharacters { count: usize, limit: usize },

    #[error("wildcard contains a double star")]
    DoubleStar,
}

fn has_double_star(wildcard: &wildcard::Wildcard<'_>) -> bool {
    let mut iter = wildcard.parsed();
    let Some(mut prev) = iter.next() else {
        return false;
    };
    for next in iter {
        if prev == WildcardToken::MetasymbolAny && next == WildcardToken::MetasymbolAny {
            return true;
        }
        prev = next;
    }
    false
}

fn validate_wildcard(
    wildcard: &wildcard::Wildcard<'_>,
    wildcard_star_limit: usize,
) -> Result<(), WildcardError> {
    // We can count all metasymbols because we disabled `?`:
    let star_count = wildcard.metasymbol_count();

    if star_count > wildcard_star_limit {
        return Err(WildcardError::TooManyStarMetacharacters {
            count: star_count,
            limit: wildcard_star_limit,
        });
    }

    if has_double_star(wildcard) {
        return Err(WildcardError::DoubleStar);
    }

    Ok(())
}

#[derive(Clone)]
pub struct Wildcard<const STRICT: bool> {
    compiled_wildcard: wildcard::Wildcard<'static>,
    /// The original pattern. We keep this to allow correct serialization of the wildcard pattern,
    /// since bytes are encoded differently depending on whether they are a valid UTF-8 sequence.
    pattern: Bytes,
}

impl<const STRICT: bool> Wildcard<STRICT> {
    pub fn new(
        pattern: Bytes,
        wildcard_star_limit: usize,
    ) -> Result<Wildcard<STRICT>, WildcardError> {
        let wildcard = wildcard::WildcardBuilder::from_owned(pattern.to_vec())
            .without_one_metasymbol()
            .case_insensitive(!STRICT)
            .build()?;

        validate_wildcard(&wildcard, wildcard_star_limit)?;

        Ok(Wildcard {
            compiled_wildcard: wildcard,
            pattern,
        })
    }

    /// Returns true if and only if the wildcard matches the input given.
    pub fn is_match(&self, input: &[u8]) -> bool {
        self.compiled_wildcard.is_match(input)
    }

    /// Returns the pattern.
    pub fn pattern(&self) -> &Bytes {
        &self.pattern
    }
}

impl<const STRICT: bool> PartialEq for Wildcard<STRICT> {
    fn eq(&self, other: &Wildcard<STRICT>) -> bool {
        self.pattern == other.pattern
    }
}

impl<const STRICT: bool> Eq for Wildcard<STRICT> {}

impl<const STRICT: bool> Hash for Wildcard<STRICT> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pattern.hash(state);
    }
}

impl<const STRICT: bool> Debug for Wildcard<STRICT> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.pattern, f)
    }
}

impl<const STRICT: bool> Serialize for Wildcard<STRICT> {
    fn serialize<S: Serializer>(&self, ser: S) -> Result<S::Ok, S::Error> {
        self.pattern.serialize(ser)
    }
}

impl<'i, 's, const STRICT: bool> LexWith<'i, &FilterParser<'s>> for Wildcard<STRICT> {
    fn lex_with(input: &'i str, parser: &FilterParser<'s>) -> LexResult<'i, Wildcard<STRICT>> {
        lex_quoted_or_raw_string(input).and_then(|(pattern, rest)| {
            match Wildcard::new(pattern, parser.settings.wildcard_star_limit) {
                Ok(wildcard) => Ok((wildcard, rest)),
                Err(err) => Err((LexErrorKind::ParseWildcard(err), input)),
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{BytesFormat, SchemeBuilder};

    #[test]
    fn test_wildcard_eq() {
        fn t<const STRICT: bool>() {
            assert_eq!(
                Wildcard::<STRICT>::new(
                    Bytes::new("a quoted string".as_bytes(), BytesFormat::Quoted),
                    usize::MAX
                )
                .unwrap(),
                Wildcard::<STRICT>::new(
                    Bytes::new("a quoted string".as_bytes(), BytesFormat::Quoted),
                    usize::MAX
                )
                .unwrap(),
            );

            // Even though they are equivalent as far as evaluation goes, they do not have the same
            // visual representation:
            assert_ne!(
                Wildcard::<STRICT>::new(
                    Bytes::new("a quoted string".as_bytes(), BytesFormat::Quoted),
                    usize::MAX
                )
                .unwrap(),
                Wildcard::<STRICT>::new(
                    Bytes::new("a quoted string".as_bytes(), BytesFormat::Raw(0)),
                    usize::MAX
                )
                .unwrap(),
            );
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_lex_quoted_string() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();

            let expr = assert_ok!(
                Wildcard::<STRICT>::lex_with(r#""a quoted string";"#, &FilterParser::new(&scheme)),
                Wildcard::<STRICT>::new(
                    Bytes::new("a quoted string".as_bytes(), BytesFormat::Quoted),
                    usize::MAX
                )
                .unwrap(),
                ";"
            );

            assert_json!(expr, "a quoted string");

            assert_err!(
                Wildcard::<STRICT>::lex_with(r#""abcd\"#, &FilterParser::new(&scheme)),
                LexErrorKind::MissingEndingQuote,
                "abcd\\"
            );
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_lex_raw_string() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();

            // Note that the `\\xaa` is escaping the `\` at the wildcard-language level, not at the
            // wirefilter-language level.

            let expr = assert_ok!(
                Wildcard::<STRICT>::lex_with(
                    r#####"r##"a raw\\xaa r#""# string"##;"#####,
                    &FilterParser::new(&scheme)
                ),
                Wildcard::<STRICT>::new(
                    Bytes::new(
                        r#####"a raw\\xaa r#""# string"#####.as_bytes(),
                        BytesFormat::Raw(2),
                    ),
                    usize::MAX
                )
                .unwrap(),
                ";"
            );

            assert_json!(expr, r#####"a raw\\xaa r#""# string"#####);

            assert_err!(
                Wildcard::<STRICT>::lex_with(r#####"r#"abc"#####, &FilterParser::new(&scheme)),
                LexErrorKind::MissingEndingQuote,
                "#\"abc"
            );
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_lex_escape_quoted_string_invalid_utf8() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();

            let bytes = [
                "a quoted ".as_bytes().to_vec(),
                vec![0xaa, 0x22],
                " string".as_bytes().to_vec(),
            ]
            .concat();

            let expr = assert_ok!(
                Wildcard::<STRICT>::lex_with(
                    r#####""a quoted \xaa\x22 string";"#####,
                    &FilterParser::new(&scheme)
                ),
                Wildcard::<STRICT>::new(
                    Bytes::new(bytes.into_boxed_slice(), BytesFormat::Quoted),
                    usize::MAX
                )
                .unwrap(),
                ";"
            );

            assert_json!(
                expr,
                [
                    97, 32, 113, 117, 111, 116, 101, 100, 32, 170, 34, 32, 115, 116, 114, 105, 110,
                    103
                ]
            );
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_lex_reject_bytes_syntax() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();

            assert_err!(
                Wildcard::<STRICT>::lex_with("61:20:71:75:6F:74", &FilterParser::new(&scheme)),
                LexErrorKind::ExpectedName("\" or r"),
                "61:20:71:75:6F:74"
            );
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_reject_invalid_wildcard() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();

            assert!(matches!(
                Wildcard::<STRICT>::lex_with(r#"r"*foo\bar*""#, &FilterParser::new(&scheme))
                    .map_err(|e| e.0),
                Err(LexErrorKind::ParseWildcard(WildcardError::InvalidWildcard(
                    _
                )))
            ));
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_star_limit() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();
            let mut parser = FilterParser::new(&scheme);

            parser.wildcard_set_star_limit(3);

            assert!(Wildcard::<STRICT>::lex_with("\"*_*_*\"", &parser).is_ok());

            assert_eq!(
                Wildcard::<STRICT>::lex_with("\"*_*_*_*\"", &parser).map_err(|e| e.0),
                Err(LexErrorKind::ParseWildcard(
                    WildcardError::TooManyStarMetacharacters { count: 4, limit: 3 }
                )),
            );
        }

        t::<false>();
        t::<true>();
    }

    #[test]
    fn test_wildcard_reject_double_star() {
        fn t<const STRICT: bool>() {
            let scheme = SchemeBuilder::new().build();

            assert!(
                Wildcard::<STRICT>::lex_with("\"*foo*bar*\"", &FilterParser::new(&scheme)).is_ok()
            );

            assert_eq!(
                Wildcard::<STRICT>::lex_with("\"*foo**bar*\"", &FilterParser::new(&scheme))
                    .map_err(|e| e.0),
                Err(LexErrorKind::ParseWildcard(WildcardError::DoubleStar)),
            );
        }

        t::<false>();
        t::<true>();
    }
}
