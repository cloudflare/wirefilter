use std::ops::RangeInclusive;

pub trait ValidateSemantics: Sized {
    fn validate_semantics(self) -> Result<Self, &'static str>;
}

impl<T: PartialOrd> ValidateSemantics for RangeInclusive<T> {
    fn validate_semantics(self) -> Result<Self, &'static str> {
        if self.start() > self.end() {
            Err("start of the range is greater than the end")
        } else {
            Ok(self)
        }
    }
}
