# Findings

Issues found while verifying OpenDP. Each is classified as a **bug** (the code violates its
documented contract), a **fragile derivation** (correct, but for undocumented reasons), or a
**tool limitation** (a workaround needed for Creusot).

## Bugs

### F1. Signed integer `inf_div` / `neg_inf_div` panic on `MIN / -1`

- **Where:** `rust/src/traits/arithmetic/mod.rs`, `impl InfDiv for` integer types.
- **What:** `i8::MIN.inf_div(&-1)` (and likewise for every signed type, and `neg_inf_div`)
  panics with "attempt to divide with overflow", in release builds too. The `Alerting*` and
  `Inf*` traits exist to return `Err` instead of panicking ("Avoids unrecoverable panics that
  could leak private information"). `alerting_div` handles this case correctly via `checked_div`.
- **How found:** Creusot could not verify the implementation (`num::Integer::div_ceil` has no
  specification), which prompted a review of its overflow behavior. Confirmed by running it.
- **Impact:** A panic where an error is promised. Integer `inf_div` is mainly used on
  parameters and distances, so whether data can reach it was not determined.
- **Fix:** Use `checked_div` (or check for `MIN / -1`) before `div_ceil` / `div_floor`.

## Fragile derivations

### D1. Pairwise float summation error uses `log2(n)` rather than `ceil(log2(n))`

- **Where:** `rust/src/transformations/sum/float/mod.rs`, `SumRelaxation for Pairwise<T>`.
- **What:** The error bound is `uk / (1 - uk) * n * max(|L|, U)` with `k = log2(n)` computed
  as a real (`inf_log2`), while the standard bound for pairwise summation (Higham, *Accuracy and
  Stability of Numerical Algorithms*, §4.2) uses the recursion depth `ceil(log2(n))`. For `n`
  not a power of two, `log2(n) < ceil(log2(n))`.
- **Why it is still sound:** The code's `u = 2^-MANTISSA_BITS` (2^-52 for `f64`) is machine
  epsilon, twice the unit roundoff of round-to-nearest. Since `2 log2(n) >= ceil(log2(n))` for all
  `n >= 2`, and `x / (1 - x)` is increasing, the bound holds.
- **Suggestion:** Document the derivation; the formal proof of the float sum must use this slack.

### D2. The sequential float overflow check relies on ties-to-even

- **Where:** `rust/src/transformations/sum/float/checked/mod.rs`,
  `CanFloatSumOverflow for Sequential<T>`, check 2.
- **What:** The check accepts `n` values bounded by `max(|L|, U)` when
  `M * n` is finite, with `M` the next power of two. The comment's justification ("the round up
  will never be by more than the next magnitude of 2") bounds a single rounding, but a sequential
  sum rounds `n` times, and past `2^p * M` (`p` = precision) every addition of `M` is a tie. Under
  round-half-to-even each tie rounds *down*, so the sum stops growing at `2^p * M`, which is why
  the check is sound (proved in Lean, `OpenDP.Float.Fmt.seq_step`). Under any other tie rule it
  is not: with 2-bit precision and `emax = 2` (largest finite value 6), bounds `[0, 1]` and
  `n = 6` pass the check, yet `1, 2, 3, 4, 5 → 6, 7 → 8` overflows.
- **Impact:** None on platforms with IEEE 754 binary arithmetic in the default rounding mode
  (Rust's semantics). Soundness depends on round-half-to-even, which is not documented.
  Platforms without exact binary64/binary32 arithmetic (x87 double rounding on `i586` targets)
  are not covered by the proof.
- **Suggestion:** Document the dependence in the check's comment and proof.

### D3. The float overflow checks rely on `inf_mul` failing on infinite results

- **Where:** `InfMul` (`rust/src/traits/arithmetic/mod.rs`), used by `can_float_sum_overflow`
  check 2: `round_up_to_nearest_power_of_two(mag)?.inf_mul(&size_).is_err()`.
- **What:** The Proof Definition of `inf_mul` only promises `out >= self * v` on success, which
  `Ok(inf)` satisfies; then check 2 would accept any size. The float implementation does return
  `Err` on non-finite results, and the trait documentation says so, but the Proof Definition, the
  part proofs rely on, does not. The same holds for the other `Inf*` operations.
- **Suggestion:** Add "and `out` is finite" to the Proof Definitions of the float `Inf*`
  operations (the Lean proof assumes it for `inf_mul`).

## Tool limitations (Creusot v0.14.0)

| Limitation | Workaround |
| --- | --- |
| Traits whose associated types refer back to themselves are rejected. | Declare them in `#[trusted]` modules. |
| Every `PartialEq` type needs a `DeepModel`; floats cannot have a sound one. | Derived/hand-written models; opaque models for carriers; trust generic float comparisons. |
| `dyn Fn` cannot be called or cloned in verified code. | Ghost models with trusted `new`/`eval`. |
| Float-to-float and int-to-float casts are unsupported. | Trust the code (casts module, float sums' overflow checks). |
| `Result::map` / `and_then` with closures defeat closure contract inference. | Use `?` instead. |
| Generic `Clone::clone` has no contract. | Avoid cloning `Copy` values. |
| Calls to `std` functions without specifications (`format!`, backtraces) are unprovable. | Trusted constructors (e.g. `err!` under Creusot). |
| Crash (`unreachable!`) in the resolve backend on `dyn Any` types. | Not reported yet; avoided by trusting the code involved. |
| Lemmas cannot be applied under quantifiers. | State theorems with explicit parameters. |
| Large conjunctive predicates time out as one goal. | Mark them `inline` so they are split. |
