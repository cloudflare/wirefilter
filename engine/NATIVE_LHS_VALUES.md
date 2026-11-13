# Reading stored values through native field bindings

`ExecutionContext` and downstream contexts expose runtime-typed `LhsValue`
fields through `FieldConsumer::native`. There is one field-binding interface;
`ExecutionContext` uses `LhsValueProvider` and the same reader available to
downstream contexts. It continues to own its field table and validate values
when they are inserted.

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
use cheap repeated access instead of enabling the memoization allocations used
for native collection conversion. Other providers keep the conservative default.

The context must check inserted values against the scheme. The return type
`&LhsValue` cannot establish a fixed logical type during startup validation.
Macro validation still checks field coverage and mandatory/optional getters.
No unsafe code or lifetime erasure is introduced.

## Evaluation comparison

The `lhs_value_reader` Criterion group evaluates the same expressions against
the same populated `ExecutionContext` through two getters:

- `execution_context`: the default family and internal field accessor.
- `public_getter`: a downstream getter using the public accessor, which checks
  the scheme on each read.

Both use `LhsValueProvider` and `LhsValueRead`. These are evaluation measurements,
excluding parsing, filter compilation and context construction. They are not FL2
phase latency or p99 measurements, and do not
measure release-build compiler memory or retained compiled-filter memory.

Reproduction:

```sh
cargo bench -p wirefilter-engine --bench bench -- lhs_value_reader --test
cargo bench -p wirefilter-engine --bench bench -- \
  lhs_value_reader --warm-up-time 0.5 --measurement-time 1 --sample-size 30
```

## Measurements before unifying the default context

The following results were collected at commit `abc1685`, before removing the
separate stored binding path. They are a baseline for the unified implementation,
not measurements of the current code. That commit's benchmark had three getters:
`stored` used the previous stored path and internal accessor; `checked_stored`
used that path with the public accessor; `lhs_reader` used the native reader and
public accessor. The reproduction commands above run those three variants when
used with that revision.

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

## Unified default context: focused repeat

After the complete 20-case run, function results varied enough to warrant a
longer comparison against the exact parent `abc1685`. The parent and unified
binaries were built separately and their benchmark lists checked. Both were
pinned to CPU 0 in the same VM, with 1 s warm-up, 3 s measurement and 40 samples
per case. The downstream control retains the same getter and family types in
both revisions. Values are slope estimates in nanoseconds per evaluation.

| Case | Parent stored | Parent reader | Unified default | Unified public getter | Default vs parent stored |
| --- | ---: | ---: | ---: | ---: | ---: |
| `array_each` | 227.49 | 190.52 | 233.31 | 199.37 | +2.6% |
| `nested_each` | 601.49 | 207.34 | 285.04 | 238.48 | -52.6% |
| `selected_function` | 54.98 | 54.62 | 54.84 | 53.18 | -0.3% |
| `map_each_function` | 1023.63 | 949.82 | 1008.42 | 940.89 | -1.5% |
| `mapped_extra_map` | 2391.63 | 2374.96 | 2322.30 | 2325.45 | -2.9% |

The large function slowdowns seen in the initial short run did not reproduce
in this comparison. These results support preserving the default context's
function behavior and improving nested traversal; they do not establish
statistical equivalence for small timing differences or an effect on FL2 p99.
The getter controls also differ despite using the same reader; the cause of
those differences has not been isolated. In particular, the unified public
getter's nested case is slower than the parent reader in this repeat. These
microbenchmarks do not establish a performance guarantee for native contexts.

## Correctness coverage

Tests exercise built-in and downstream contexts for scalar values, optional roots,
missing children, and 63 runtime-selected nested collection shapes. They check
container, map-key and payload identity, custom compiler comparisons, ignored
function arguments, mapped extra arguments, and the existing `map[*]` function
argument behavior. The benchmark verifies matching results before timing each
case. A separate path-validation test rejects invalid index types and mismatched
predicate input types.

Workspace tests and all-feature engine tests pass after unification. Without
default features, two existing tests unconditionally execute regex expressions:
`ast::field_expr::tests::test_raw_string` and
`context::tests::test_native_complete_operator_and_collection_paths`. Both also
fail at the original `8d3e22a` revision because regex support is disabled. The
remaining 204 library tests and six reader integration tests pass with those two
tests excluded.

## Retained compiled-filter allocations

A separate counting-allocator diagnostic compares the exact parent `abc1685`
with the unified default context. It measures live requested bytes and allocation
counts after parsing and compilation, with the scheme constructed beforehand.
Each expression is warmed first; three repetitions agree, and dropping each
filter restores the initial live counts. These are debug-build measurements on
AArch64 with rustc 1.100.0 and default features, using the system allocator. They
exclude allocator metadata, stack storage and process RSS; optimized builds may
produce different allocation sizes.

| Case | Before: bytes / allocations | Unified: bytes / allocations |
| --- | ---: | ---: |
| Boolean | 24 / 1 | 40 / 1 |
| Integer ordering | 32 / 1 | 48 / 1 |
| Optional integer | 32 / 1 | 48 / 1 |
| Bytes equality | 64 / 2 | 80 / 2 |
| Bytes contains | 181 / 2 | 197 / 2 |
| IP membership | 65 / 2 | 81 / 2 |
| Indexed array | 72 / 2 | 72 / 2 |
| Flat array `[*]` | 64 / 2 | 88 / 3 |
| Nested array iteration | 112 / 3 | 112 / 3 |
| Indexed map | 117 / 4 | 117 / 4 |
| Selected map with trailing `[*]` | 109 / 5 | 133 / 5 |
| Nested map iteration | 127 / 4 | 127 / 4 |

The shared reader captures a path even for an unindexed scalar, adding 16 bytes
to those closures. A trailing `[*]` occupies another 24-byte path entry; a flat
array comparison therefore needs one path allocation where the previous stored
implementation captured an empty path. These are retained compilation costs,
not allocations added to each evaluation. Specializing empty paths and terminal
`[*]` paths is a possible follow-up; this change keeps one reader implementation.
