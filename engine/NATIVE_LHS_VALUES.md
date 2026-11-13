# Reading stored values through native field bindings

`ExecutionContext` and downstream contexts expose runtime-typed `LhsValue`
fields through `FieldConsumer::consume`. There is one field-binding interface;
`ExecutionContextFamily` binds `ExecutionContext` fields through `LhsValueProvider`
and the same reader available to downstream contexts. `ExecutionContext`
continues to own its field table and validate values when they are inserted.

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

At `9703c08`, workspace tests and all-feature engine tests passed after unification. Without
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

## Shared traversal refactor

The refactor uses `FieldConsumer::consume` and `ExecutionContextFamily`, shares
array-comparison compilation, and reuses `LhsValue` traversal for function results
and custom collection comparisons. The measurements below compare that change
with the exact `9703c08` parent. The context-state representation is unchanged.

The new `reader_traversal` benchmark covers 22 cases: scalar/indexed/flat/nested
function comparisons; borrowed and owned function results; root and flattened
value results; implicit Boolean-array iteration; ordinary typed native fields;
and native custom-collection comparison fallbacks. The existing 20-case
`lhs_value_reader` group remains available. Value-selection cases compile an
`IndexExpr` directly, matching the expression used inside function arguments;
top-level value parsing deliberately rejects `[*]` selections.

### Allocations

A standalone counting system allocator measures requested bytes and live blocks
in debug builds with default features on AArch64/rustc 1.100.0. Schemes and request
values are constructed before the snapshots. Each case is warmed and repeated
three times; the counts agree, and dropping each result restores the original
live bytes and blocks.

**Retained compiled-expression allocations are unchanged in all 26 measured cases.**
This includes unindexed, indexed, flat and nested function comparisons; root and
flattened function values; ordinary typed native scalar/array/nested fields; and
custom native collection comparisons. The empty-path function closures remain
compact. This does not remove the previously documented `LhsValue` field-reader
storage overhead.

Per-evaluation changes are:

| Case | Allocation/reallocation operations before → after | Sum of requested bytes before → after | Peak additional live requested bytes before → after |
| --- | ---: | ---: | ---: |
| Nested borrowed function comparison | 6 → 4 | 6112 → 5760 | 3232 → 3072 |
| Nested owned function comparison | 15 → 13 | 9568 → 9216 | 5152 → 6528 |
| Flatten borrowed function value | 6 → 4 | 6112 → 5760 | 3232 → 3072 |
| Flatten owned function value | 15 → 13 | 9568 → 9216 | 5152 → 4992 |
| Nested native custom-collection comparison | 25 → 24 | 5536 → 5376 | 4192 → 4800 |

The other 21 cases have unchanged allocation operations, requested-byte totals
and peaks. Requested-byte totals include each successful allocation and
reallocation's requested size; they are neither retained bytes nor process RSS.
Peak values track live requested storage above the pre-evaluation baseline and
exclude allocator metadata or any internal transient memory during reallocation.

The owned comparison cases expose a trade-off: borrowing the temporary result
for comparison keeps its child containers alive until traversal finishes, while
the former iterator dropped consumed children progressively. Consequently,
allocation traffic falls but peak requested live memory rises by 1376 bytes for
the owned nested function fixture and 608 bytes for the custom-collection fixture.
The consuming value-selection path continues to move owned values into its
result, so its peak decreases instead. These fixtures use 64 integer elements;
they do not establish peak-memory behavior for arbitrary function results.

### Evaluation time

The exact `9703c08` parent and the final refactor were built with the same
extended benchmark harness (apart from adapting the renamed consumer method).
These are Linux AArch64/rustc 1.100.0 measurements using the optimized Cargo bench
profile, inheriting `[profile.release] lto = true`. Codegen units were not
overridden; Cargo defaults apply. Saved binaries ran sequentially on CPU 0, with
no concurrent Cargo builds. The final focused pair used 40 samples, 1 s warm-up
and 3 s measurement. The parent was rerun immediately after the final binary;
the figures below do not reuse the older diagnostic baseline timings.

Values are Criterion slope point estimates in nanoseconds. Negative changes
mean faster evaluation. This compares against the parent of this refactor,
not upstream Wirefilter. It measures neither FL2 phase latency/p99 nor rustc
peak build memory.

| Case | Parent (ns) | Refactor (ns) | Change |
| --- | ---: | ---: | ---: |
| `custom_native_flat` | 274.52 | 269.55 | -1.8% |
| `custom_native_index` | 237.41 | 237.53 | +0.1% |
| `custom_native_nested` | 730.92 | 681.96 | -6.7% |
| `custom_native_root` | 235.67 | 235.14 | -0.2% |
| `function_flat_borrowed` | 264.31 | 242.90 | -8.1% |
| `function_flat_owned` | 548.15 | 506.14 | -7.7% |
| `function_index` | 10.59 | 11.37 | +7.4% |
| `function_nested_borrowed` | 609.87 | 254.37 | -58.3% |
| `function_nested_owned` | 1026.59 | 748.56 | -27.1% |
| `function_scalar` | 8.02 | 7.93 | -1.2% |
| `implicit_bool_array` | 189.62 | 194.37 | +2.5% |
| `implicit_bool_function_borrowed` | 200.86 | 199.34 | -0.8% |
| `implicit_bool_function_owned` | 429.94 | 414.51 | -3.6% |
| `implicit_bool_native` | 262.21 | 271.98 | +3.7% |
| `native_array` | 158.66 | 144.16 | -9.1% |
| `native_nested` | 174.92 | 172.05 | -1.6% |
| `native_scalar` | 1.36 | 1.40 | +2.3% |
| `value_flat_borrowed` | 7.84 | 7.72 | -1.6% |
| `value_nested_borrowed` | 593.32 | 426.96 | -28.0% |
| `value_nested_owned` | 953.25 | 744.67 | -21.9% |
| `value_root_borrowed` | 7.82 | 7.71 | -1.4% |
| `value_root_owned` | 467.67 | 470.48 | +0.6% |

Nested function comparisons improved by 58% for borrowed results and 27% for
owned results. Flattening nested function values improved by 28%/22%, and the
nested native custom-comparison fallback improved by 7%. These gains accompany
the allocation reductions above. Indexed scalar function comparison increased
from 10.59 to 11.37 ns; implicit Boolean-array iteration increased by 2.5% for
`ExecutionContext` and 3.7% for the typed native context.

These small fixtures have observable run sensitivity. Earlier diagnostic runs
of the unchanged typed nested benchmark changed direction depending on the
benchmark filter/order; an assembly audit of that pair found identical comparison
closure and row-loop instructions after normalizing relocations. The final
matched full-group run measured 174.92 → 172.05 ns. It does not establish a
typed-native speedup, and the small scalar/flat-case differences should not be
extrapolated to whole-phase latency.

An intermediate extraction of the child-comparison loop introduced an extra
function boundary per visited collection; map iteration was slower in that
version. The final implementation keeps the recursive loop together; final
measurements of the affected existing controls are below.

The control subset was rerun as a matched parent/final pair with the identical
filter and order, using 30 samples, 0.5 s warm-up and 1 s measurement. Earlier
full-group control timings are not used in this table.

| Case | Internal parent → refactor (ns) | Change | Public parent → refactor (ns) | Change |
| --- | ---: | ---: | ---: | ---: |
| `array_each` | 232.49 → 240.87 | +3.6% | 195.04 → 199.70 | +2.4% |
| `nested_each` | 236.15 → 243.18 | +3.0% | 229.81 → 216.58 | -5.8% |
| `map_each` | 734.30 → 763.86 | +4.0% | 676.81 → 709.17 | +4.8% |
| `map_each_function` | 1042.12 → 1023.55 | -1.8% | 972.06 → 960.86 | -1.2% |

The final control pair still shows map iteration 4.0–4.8% slower and flat array
iteration 2.4–3.6% slower. Nested stored iteration changes direction between the
two getter modes (+3.0% internal, −5.8% public), while mapped functions are within
1–2%. The shared traversal therefore improves the targeted function-result cases
without demonstrating a uniform evaluation speedup. The cause of these remaining
control differences is not established by the measurements.

Reproduce the focused group with:

```sh
cargo bench --locked -p wirefilter-engine --bench bench -- \
  reader_traversal --warm-up-time 1 --measurement-time 3 --sample-size 40
```

### Validation

The final refactor passes workspace tests, engine tests with all features,
engine tests without default features (excluding the two existing regex-dependent
cases listed above), Clippy for all targets/features, rustdoc with warnings denied,
and formatting/diff checks. The saved parent and final benchmark binaries list
the same 22 focused cases and pass their benchmark smoke checks. Allocation
diagnostics were rerun after the final comparison-loop adjustment and produce
identical counts to those reported above.
