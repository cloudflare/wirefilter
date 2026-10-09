use super::{FilterAst, FilterValueAst};
use crate::functions::{FunctionDefinition, FunctionSettings};
use crate::lex::{LexErrorKind, LexResult, LexWith, complete};
use crate::scheme::Scheme;
use std::cmp::{max, min};
use std::error::Error;
use std::fmt::{self, Debug, Display, Formatter};

/// An opaque filter parsing error associated with the original input.
///
/// For now, you can just print it in a debug or a human-readable fashion.
#[derive(Debug, PartialEq)]
pub struct ParseError<'i> {
    /// The error that occurred when parsing the input
    pub(crate) kind: LexErrorKind,

    /// The input that caused the parse error
    pub(crate) input: &'i str,

    /// The line number on the input where the error occurred
    pub(crate) line_number: usize,

    /// The start of the bad input
    pub(crate) span_start: usize,

    /// The number of characters that span the bad input
    pub(crate) span_len: usize,
}

impl Error for ParseError<'_> {}

impl<'i> ParseError<'i> {
    /// Create a new ParseError for the input, LexErrorKind and span in the
    /// input.
    pub fn new(mut input: &'i str, (kind, span): (LexErrorKind, &'i str)) -> Self {
        let input_range = input.as_ptr() as usize..=input.as_ptr() as usize + input.len();
        assert!(
            input_range.contains(&(span.as_ptr() as usize))
                && input_range.contains(&(span.as_ptr() as usize + span.len()))
        );
        let mut span_start = span.as_ptr() as usize - input.as_ptr() as usize;

        let (line_number, line_start) = input[..span_start]
            .match_indices('\n')
            .map(|(pos, _)| pos + 1)
            .scan(0, |line_number, line_start| {
                *line_number += 1;
                Some((*line_number, line_start))
            })
            .last()
            .unwrap_or_default();

        input = &input[line_start..];

        span_start -= line_start;
        let mut span_len = span.len();

        if let Some(line_end) = input.find('\n') {
            input = &input[..line_end];
            span_len = min(span_len, line_end - span_start);
        }

        ParseError {
            kind,
            input,
            line_number,
            span_start,
            span_len,
        }
    }
}

impl Display for ParseError<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "Filter parsing error ({}:{}):",
            self.line_number + 1,
            self.span_start + 1
        )?;

        writeln!(f, "{}", self.input)?;

        for _ in 0..self.span_start {
            write!(f, " ")?;
        }

        for _ in 0..max(1, self.span_len) {
            write!(f, "^")?;
        }

        writeln!(f, " {}", self.kind)?;

        Ok(())
    }
}

/// Parser settings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParserSettings {
    /// Approximate size of the cache used by the DFA of a regex.
    /// Default: 10MB
    pub regex_dfa_size_limit: usize,
    /// Approximate size limit of the compiled regular expression.
    /// Default: 2MB
    pub regex_compiled_size_limit: usize,
    /// Maximum number of star metacharacters allowed in a wildcard.
    /// Default: unlimited
    pub wildcard_star_limit: usize,
    /// Maximum nesting depth allowed while parsing.
    /// Default: 128
    pub max_nesting_depth: u16,
    /// Settings for custom functions registered by embedders.
    /// Default: empty
    pub function_settings: FunctionSettings,
}

impl Default for ParserSettings {
    #[inline]
    fn default() -> Self {
        Self {
            // Default value extracted from the regex crate.
            regex_compiled_size_limit: 10 * (1 << 20),
            // Default value extracted from the regex crate.
            regex_dfa_size_limit: 2 * (1 << 20),
            wildcard_star_limit: usize::MAX,
            max_nesting_depth: 128,
            function_settings: FunctionSettings::default(),
        }
    }
}

impl ParserSettings {
    /// Sets settings shared by every registration of function definition type `F`.
    ///
    /// This replaces any previously configured value for `F`.
    pub fn set_function_settings<F: FunctionDefinition + 'static>(
        &mut self,
        settings: F::Settings,
    ) {
        self.function_settings.set::<F>(settings);
    }
}

/// A structure used to drive parsing of an expression into a [`FilterAst`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FilterParser<'s> {
    pub(crate) scheme: &'s Scheme,
    pub(crate) settings: ParserSettings,
}

impl<'s> FilterParser<'s> {
    /// Creates a new parser with default settings.
    #[inline]
    pub fn new(scheme: &'s Scheme) -> Self {
        Self {
            scheme,
            settings: ParserSettings::default(),
        }
    }

    /// Creates a new parser with the specified settings.
    #[inline]
    pub fn with_settings(scheme: &'s Scheme, settings: ParserSettings) -> Self {
        Self { scheme, settings }
    }

    /// Returns the [`Scheme`](struct@Scheme) for which this parser has been constructor for.
    #[inline]
    pub fn scheme(&self) -> &'s Scheme {
        self.scheme
    }

    /// Creates a parsing context borrowing this parser.
    #[inline]
    pub fn context(&self) -> ParserContext<'_> {
        ParserContext::new(self)
    }

    #[inline]
    pub(crate) fn lex_as<'i, L>(&self, input: &'i str) -> LexResult<'i, L>
    where
        L: for<'p, 'c> LexWith<'i, &'p ParserContext<'c>>,
    {
        self.context().lex_as(input)
    }

    /// Parses a filter expression into an AST form.
    pub fn parse<'i>(&self, input: &'i str) -> Result<FilterAst, ParseError<'i>> {
        complete(self.lex_as(input.trim())).map_err(|err| ParseError::new(input, err))
    }

    /// Parses a value expression into an AST form.
    pub fn parse_value<'i>(&self, input: &'i str) -> Result<FilterValueAst, ParseError<'i>> {
        complete(self.lex_as(input.trim())).map_err(|err| ParseError::new(input, err))
    }

    /// Retrieve parser settings.
    #[inline]
    pub fn settings(&self) -> &ParserSettings {
        &self.settings
    }

    /// Set the approximate size limit of the compiled regular expression.
    #[inline]
    pub fn regex_set_compiled_size_limit(&mut self, regex_compiled_size_limit: usize) {
        self.settings.regex_compiled_size_limit = regex_compiled_size_limit;
    }

    /// Get the approximate size limit of the compiled regular expression.
    #[inline]
    pub fn regex_get_compiled_size_limit(&self) -> usize {
        self.settings.regex_compiled_size_limit
    }

    /// Set the approximate size of the cache used by the DFA of a regex.
    #[inline]
    pub fn regex_set_dfa_size_limit(&mut self, regex_dfa_size_limit: usize) {
        self.settings.regex_dfa_size_limit = regex_dfa_size_limit;
    }

    /// Get the approximate size of the cache used by the DFA of a regex.
    #[inline]
    pub fn regex_get_dfa_size_limit(&self) -> usize {
        self.settings.regex_dfa_size_limit
    }

    /// Set the maximum number of star metacharacters allowed in a wildcard.
    #[inline]
    pub fn wildcard_set_star_limit(&mut self, wildcard_star_limit: usize) {
        self.settings.wildcard_star_limit = wildcard_star_limit;
    }

    /// Get the maximum number of star metacharacters allowed in a wildcard.
    #[inline]
    pub fn wildcard_get_star_limit(&self) -> usize {
        self.settings.wildcard_star_limit
    }

    /// Set the maximum nesting depth allowed while parsing.
    #[inline]
    pub fn set_max_nesting_depth(&mut self, max_nesting_depth: u16) {
        self.settings.max_nesting_depth = max_nesting_depth;
    }

    /// Get the maximum nesting depth allowed while parsing.
    #[inline]
    pub fn max_nesting_depth(&self) -> u16 {
        self.settings.max_nesting_depth
    }

    /// Sets settings shared by every registration of function definition type `F`.
    ///
    /// This replaces any previously configured value for `F`.
    #[inline]
    pub fn set_function_settings<F: FunctionDefinition + 'static>(
        &mut self,
        settings: F::Settings,
    ) {
        self.settings.set_function_settings::<F>(settings);
    }
}

/// Read-only parser configuration and per-parse state used by lexer implementations.
///
/// Create a context with [`FilterParser::context`]. Nesting state is managed internally while
/// parsing an expression.
#[derive(Clone, Copy)]
pub struct ParserContext<'a> {
    parser: &'a FilterParser<'a>,
    current_nesting_depth: u16,
}

impl<'a> ParserContext<'a> {
    fn new(parser: &'a FilterParser<'a>) -> Self {
        Self {
            parser,
            current_nesting_depth: 0,
        }
    }

    pub(crate) fn lex_as<'i, L>(&self, input: &'i str) -> LexResult<'i, L>
    where
        L: for<'p> LexWith<'i, &'p Self>,
    {
        L::lex_with(input, self)
    }

    pub(crate) fn with_increased_nesting<'i>(
        &self,
        span: &'i str,
    ) -> Result<Self, (LexErrorKind, &'i str)> {
        if self.current_nesting_depth >= self.parser.settings.max_nesting_depth {
            Err((
                LexErrorKind::NestingLimitExceeded {
                    limit: self.parser.settings.max_nesting_depth,
                },
                span,
            ))
        } else {
            let mut nested = *self;
            nested.current_nesting_depth += 1;
            Ok(nested)
        }
    }

    /// Returns the parser settings used by this context.
    #[inline]
    pub fn settings(&self) -> &ParserSettings {
        self.parser.settings()
    }

    /// Returns the scheme used by this context.
    #[inline]
    pub fn scheme(&self) -> &Scheme {
        self.parser.scheme()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        CompiledFunction, FunctionCallExpr, FunctionDefinition, FunctionDefinitionContext,
        FunctionParam, FunctionParamError, SchemeBuilder, Type,
    };
    use std::sync::atomic::{AtomicUsize, Ordering};

    static FUNCTION_SETTINGS_CLONES: AtomicUsize = AtomicUsize::new(0);

    #[derive(Debug, Eq, PartialEq)]
    struct CloneCountingFunctionSettings;

    impl Clone for CloneCountingFunctionSettings {
        fn clone(&self) -> Self {
            FUNCTION_SETTINGS_CLONES.fetch_add(1, Ordering::Relaxed);
            Self
        }
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct TestFunctionSettings {
        limit: usize,
    }

    #[derive(Debug)]
    struct SettingsAwareFunction;

    impl FunctionDefinition for SettingsAwareFunction {
        type Settings = TestFunctionSettings;

        fn context(&self, settings: &ParserSettings) -> Option<FunctionDefinitionContext> {
            let settings = settings.function_settings.get::<Self>()?;
            Some(FunctionDefinitionContext::new(settings.limit))
        }

        fn check_param(
            &self,
            _: &ParserSettings,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: &FunctionParam<'_>,
            _: Option<&mut FunctionDefinitionContext>,
        ) -> Result<(), FunctionParamError> {
            unreachable!("settings_aware takes no arguments")
        }

        fn return_type(
            &self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<&FunctionDefinitionContext>,
        ) -> Type {
            Type::Bool
        }

        fn arg_count(&self) -> (usize, Option<usize>) {
            (0, Some(0))
        }

        fn compile(
            &self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<FunctionDefinitionContext>,
        ) -> CompiledFunction {
            Box::new(|_| None)
        }
    }

    #[derive(Debug)]
    struct CloneCountingFunction;

    impl FunctionDefinition for CloneCountingFunction {
        type Settings = CloneCountingFunctionSettings;

        fn check_param(
            &self,
            _: &ParserSettings,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: &FunctionParam<'_>,
            _: Option<&mut FunctionDefinitionContext>,
        ) -> Result<(), FunctionParamError> {
            unreachable!("clone_counting takes no arguments")
        }

        fn return_type(
            &self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<&FunctionDefinitionContext>,
        ) -> Type {
            Type::Bool
        }

        fn arg_count(&self) -> (usize, Option<usize>) {
            (0, Some(0))
        }

        fn compile(
            &self,
            _: &mut dyn ExactSizeIterator<Item = FunctionParam<'_>>,
            _: Option<FunctionDefinitionContext>,
        ) -> CompiledFunction {
            Box::new(|_| None)
        }
    }

    #[test]
    fn nested_parsing_does_not_clone_function_settings() {
        let mut builder = SchemeBuilder::new();
        builder.add_field("flag", Type::Bool).unwrap();
        let scheme = builder.build();
        let mut parser = FilterParser::new(&scheme);
        parser.set_function_settings::<CloneCountingFunction>(CloneCountingFunctionSettings);
        FUNCTION_SETTINGS_CLONES.store(0, Ordering::Relaxed);

        parser.parse("(((flag)))").unwrap();

        assert_eq!(FUNCTION_SETTINGS_CLONES.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn function_context_receives_parser_settings() {
        let mut builder = SchemeBuilder::new();
        builder
            .add_function("settings_aware", SettingsAwareFunction)
            .unwrap();
        let scheme = builder.build();

        let parser = FilterParser::new(&scheme);
        let (function, _) = parser
            .lex_as::<FunctionCallExpr>("settings_aware()")
            .unwrap();
        assert!(function.context().is_none());

        let mut parser = FilterParser::new(&scheme);
        parser.set_function_settings::<SettingsAwareFunction>(TestFunctionSettings { limit: 42 });
        let (function, _) = parser
            .lex_as::<FunctionCallExpr>("settings_aware()")
            .unwrap();
        assert_eq!(
            function.context().unwrap().downcast_ref::<usize>(),
            Some(&42)
        );
    }

    #[test]
    fn function_settings_store_values_by_function_type() {
        let mut settings = FunctionSettings::default();
        assert!(settings.get::<SettingsAwareFunction>().is_none());
        assert!(settings.get::<CloneCountingFunction>().is_none());

        settings.set::<SettingsAwareFunction>(TestFunctionSettings { limit: 42 });
        settings.set::<CloneCountingFunction>(CloneCountingFunctionSettings);
        assert_eq!(
            settings.get::<SettingsAwareFunction>(),
            Some(&TestFunctionSettings { limit: 42 })
        );
        assert_eq!(
            settings.get::<CloneCountingFunction>(),
            Some(&CloneCountingFunctionSettings)
        );

        let original = settings.clone();
        assert_eq!(settings, original);

        settings.set::<SettingsAwareFunction>(TestFunctionSettings { limit: 7 });
        assert_ne!(settings, original);
        assert_eq!(
            settings.get::<SettingsAwareFunction>(),
            Some(&TestFunctionSettings { limit: 7 })
        );
        assert_eq!(
            settings.get::<CloneCountingFunction>(),
            Some(&CloneCountingFunctionSettings)
        );
    }

    #[test]
    fn registrations_of_same_function_type_share_settings() {
        let mut builder = SchemeBuilder::new();
        builder
            .add_function("settings_aware_one", SettingsAwareFunction)
            .unwrap();
        builder
            .add_function("settings_aware_two", SettingsAwareFunction)
            .unwrap();
        let scheme = builder.build();
        let mut parser = FilterParser::new(&scheme);
        parser.set_function_settings::<SettingsAwareFunction>(TestFunctionSettings { limit: 42 });

        for name in ["settings_aware_one()", "settings_aware_two()"] {
            let (function, _) = parser.lex_as::<FunctionCallExpr>(name).unwrap();
            assert_eq!(
                function.context().unwrap().downcast_ref::<usize>(),
                Some(&42)
            );
        }
    }
}
