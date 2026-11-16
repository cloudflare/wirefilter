use wirefilter::{CompiledRegex, ParserSettings, Regex, RegexFormat};

#[test]
#[cfg_attr(
    not(feature = "regex"),
    should_panic(expected = "Engine was built without regex support")
)]
fn extracted_regex_matches_through_public_api() {
    let regex: CompiledRegex = Regex::new("a.b", RegexFormat::Literal, &ParserSettings::default())
        .unwrap()
        .into_compiled();
    assert!(regex.is_match(b"a\xffb"));
    assert!(!regex.is_match(b"ac"));
}
