// This is up here to make the Scheme macro happy
#[cfg(fuzzing)]
use wirefilter::Scheme;

#[cfg(fuzzing)]
fn main() {
    fuzz!(|data: &[u8]| {
        let scheme = Scheme! { foo: Bytes };
        let mut input = String::from(String::from_utf8_lossy(data));

        input = input.replace("\"###", "x");
        let f = format!("foo == r###\"{}\"###", &input);
        scheme.parse(&f).unwrap().compile();

        input = input.replace("\"##", "x");
        let f = format!("foo == r##\"{}\"##", &input);
        scheme.parse(&f).unwrap().compile();

        input = input.replace("\"#", "x");
        let f = format!("foo == r#\"{}\"#", &input);
        scheme.parse(&f).unwrap().compile();

        input = input.replace("\"", "x");
        let f = format!("foo == r\"{}\"", &input);
        scheme.parse(&f).unwrap().compile();
    });
}

#[cfg(not(fuzzing))]
fn main() {
    panic!("must compile with `cargo afl build`, not `cargo build`")
}
