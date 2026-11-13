# Reading stored values through native field bindings

This change lets a downstream context store runtime-typed `LhsValue` fields and
expose them through `FieldConsumer::native`. It retains the existing stored
binding path so the two implementations can be reviewed and compared.

## Interfaces

`LhsValueProvider` supplies a getter returning `&LhsValue`, with both the reference
and its payloads valid for the evaluation borrow. The context can own its values
or borrow them from another owner. See the runnable example in `native/mod.rs`
and the independent context in `tests/native_lhs_values.rs`.

`FieldValueType` describes a field root. Every existing static `ValueType`
implements it automatically. `LhsValueType` instead gets the root type from the
scheme and validates the complete index path during filter compilation. It
supports arbitrary array/map nesting without enumerating combinations in Rust.
Native collection elements still have static types: this does not make
`Vec<LhsValue>` a native array.

`LhsValueRead` borrows existing containers, follows concrete indices and `[*]`
selections, and calls the compiler's existing `Compare::compare` method on each
selected value. This includes custom comparisons on entire arrays or maps.
Function arguments borrow selected containers instead of reconstructing them.
Flattening multiple selections and producing comparison results can still
allocate output containers.

`IntoLhsValue::MATERIALIZES_COLLECTIONS` distinguishes borrowing existing
containers from converting native collections. Borrowed `LhsValue` arguments
retain the stored path's cheap repeated access instead of enabling the
memoization allocations used for native collection conversion. Other providers
keep the conservative default.

The context must check inserted values against the scheme. The return type
`&LhsValue` cannot establish a fixed logical type during startup validation.
Macro validation still checks field coverage and mandatory/optional getters.
No unsafe code or lifetime erasure is introduced.

## Evaluation comparison

The `lhs_value_reader` Criterion group evaluates the same expressions against
the same populated `ExecutionContext` through three bindings:

- `stored`: the existing stored path and internal field accessor.
- `checked_stored`: a downstream stored getter using the public accessor, which
  checks the scheme on each read.
- `lhs_reader`: the new native reader using that same public accessor.

The checked control separates public-accessor costs from reader costs. These
are evaluation measurements, excluding parsing, filter compilation and context
construction. They are not FL2 phase latency or p99 measurements, and do not
measure release-build compiler memory or retained compiled-filter memory.

Reproduction:

```sh
cargo bench -p wirefilter-engine --bench bench -- lhs_value_reader --test
cargo bench -p wirefilter-engine --bench bench -- \
  lhs_value_reader --warm-up-time 0.5 --measurement-time 1 --sample-size 30
```

## Local measurements

Linux AArch64 VM, rustc 1.100.0, Cargo's optimized bench profile with the
workspace's `lto = true`. One run per case, 30 samples, 0.5 s warm-up and 1 s
measurement. Values below are Criterion's slope point estimates in nanoseconds
per evaluation; the last column compares the new reader with `checked_stored`.
Negative changes mean less evaluation time. Small differences need longer
repeated runs before drawing conclusions; these are not statistical equivalence
claims.

| Case | Stored (ns) | Checked stored (ns) | Lhs reader (ns) | Reader vs checked |
| --- | ---: | ---: | ---: | ---: |
| `array_each` | 257.04 | 200.38 | 190.07 | -5.1% |
| `array_function` | 11.12 | 10.84 | 10.95 | +1.0% |
| `array_index` | 2.98 | 3.13 | 3.28 | +4.6% |
| `array_missing` | 2.67 | 2.78 | 2.89 | +3.9% |
| `bool` | 1.06 | 1.35 | 1.64 | +20.8% |
| `bytes_contains` | 3.70 | 4.08 | 4.06 | -0.4% |
| `bytes_equal` | 2.10 | 2.42 | 2.55 | +5.3% |
| `custom_each_array` | 24.47 | 24.19 | 22.74 | -6.0% |
| `custom_map` | 1.29 | 1.55 | 1.63 | +5.1% |
| `custom_selected_array` | 7.28 | 7.55 | 7.50 | -0.7% |
| `integer_ordering` | 1.08 | 1.45 | 1.60 | +10.3% |
| `ip_membership` | 2.18 | 2.32 | 2.71 | +16.8% |
| `map_each` | 1942.84 | 1743.30 | 772.58 | -55.7% |
| `map_each_function` | 1017.13 | 941.92 | 948.38 | +0.7% |
| `map_function` | 10.33 | 9.85 | 9.86 | +0.1% |
| `map_index` | 12.08 | 12.07 | 12.14 | +0.6% |
| `map_missing` | 7.56 | 7.53 | 7.43 | -1.3% |
| `mapped_extra_map` | 2435.79 | 2281.65 | 2283.05 | +0.1% |
| `nested_each` | 588.37 | 513.84 | 204.03 | -60.3% |
| `selected_function` | 58.08 | 56.57 | 55.11 | -2.6% |

The reader is not zero-overhead: scalar/indexed cases can add fractions of a
nanosecond, and the exact difference depends on the expression. Nested array and
map traversal is substantially faster in this run. The reader walks borrowed
children directly, avoiding the stored path's general `MapEachIterator` for
multi-step selections. Function-argument measurements remain close to the
checked control, consistent with retaining cheap borrowed conversion.

The two stored controls also differ in some collection cases despite sharing
the traversal implementation. Getter specialization and generated code can
affect these results, so subtracting the controls does not isolate a universal
cost for the scheme check.

## Correctness coverage

Tests compare stored and native execution for scalar values, optional roots,
missing children, and 63 runtime-selected nested collection shapes. They check
container, map-key and payload identity, custom compiler comparisons, ignored
function arguments, mapped extra arguments, and the existing `map[*]` function
argument behavior. The benchmark verifies matching results before timing each
case. A separate path-validation test rejects invalid index types and mismatched
predicate input types.
