# Wirefilter

[![Build status](https://img.shields.io/travis/com/cloudflare/wirefilter/master.svg)](https://travis-ci.com/cloudflare/wirefilter)
[![Crates.io](https://img.shields.io/crates/v/wirefilter-engine.svg)](https://crates.io/crates/wirefilter-engine)
[![License](https://img.shields.io/github/license/cloudflare/wirefilter.svg)](LICENSE)

This is an execution engine for [Wireshark®](https://www.wireshark.org/)-like filters.

It contains public APIs for parsing filter syntax, compiling them into
an executable IR and, finally, executing filters against provided values.

## Example

```rust
use wirefilter::{ExecutionContext, Scheme, Type};

fn main() -> Result<(), failure::Error> {
    // Create a map of possible filter fields.
    let scheme = Scheme! {
        http.method: Bytes,
        http.ua: Bytes,
        port: Int,
    };

    // Parse a Wireshark-like expression into an AST.
    let ast = scheme.parse(r#"
        http.method != "POST" &&
        not http.ua matches "(googlebot|facebook)" &&
        port in {80 443}
    "#)?;

    println!("Parsed filter representation: {:?}", ast);

    // Compile the AST into an executable filter.
    let filter = ast.compile();

    // Set runtime field values to test the filter against.
    let mut ctx = ExecutionContext::new(&scheme);

    ctx.set_field_value(scheme.get_field("http.method").unwrap(), "GET")?;

    ctx.set_field_value(
        scheme.get_field("http.ua").unwrap(),
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:66.0) Gecko/20100101 Firefox/66.0",
    )?;

    ctx.set_field_value(scheme.get_field("port").unwrap(), 443)?;

    // Execute the filter with given runtime values.
    println!("Filter matches: {:?}", filter.execute(&ctx)?); // true

    // Amend one of the runtime values and execute the filter again.
    ctx.set_field_value(scheme.get_field("port").unwrap(), 8080)?;

    println!("Filter matches: {:?}", filter.execute(&ctx)?); // false

    Ok(())
}
```

## Fuzzing

There are fuzz tests in the fuzz directory.

Install afl:

```
cargo install afl --force
```

Build `bytes` fuzz test:

```
cd fuzz/bytes
cargo afl build
```

Run fuzz test (from inside `fuzz/bytes` directory):

```
cargo afl fuzz -i in -o out ../../target/debug/fuzz-bytes
```

If you see an error like:

```
Looks like the target binary is not instrumented!
```

Try deleting the compiled binary and re-building with `cargo afl build`.

## Licensing

Licensed under the MIT license. See the [LICENSE](LICENSE) file for details.
