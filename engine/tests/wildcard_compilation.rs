use wirefilter::{BytesExpr, BytesFormat, CompiledWildcard, Wildcard};

#[test]
fn extracted_wildcards_preserve_case_sensitivity_through_public_api() {
    let pattern = BytesExpr::new(b"Ab*".as_slice(), BytesFormat::Quoted);
    let strict: Wildcard<true> = Wildcard::new(pattern.clone(), usize::MAX).unwrap();
    let insensitive: Wildcard<false> = Wildcard::new(pattern, usize::MAX).unwrap();
    for (wildcard, mixed_case_matches) in [
        (strict.into_compiled(), false),
        (insensitive.into_compiled(), true),
    ] {
        let wildcard: CompiledWildcard = wildcard;
        assert!(wildcard.is_match(b"Ab\xff"));
        assert_eq!(wildcard.is_match(b"aB\xff"), mixed_case_matches);
        assert!(!wildcard.is_match(b"xxAb"));
    }
}
