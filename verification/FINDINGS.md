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

### F2. The pairwise ordered float sums underestimate their sensitivity

- **Where:** `rust/src/transformations/sum/float/ordered/mod.rs`,
  `make_(sized_)bounded_float_ordered_sum::<Pairwise<T>>`, reached from `make_sum` for `f32` and
  `f64` whenever the checked sum could overflow (the default `S` is also `Pairwise`).
- **What:** The sum uses saturating addition, `clamp(a + b, MIN, MAX)`, over the pairwise split.
  The map's derivation compares with the ideal sum (`|BS*(v) - BS(v)| <= error`), but a saturated
  sum can be arbitrarily far from the ideal sum. Clamping depends on how elements are grouped, and
  inserting or deleting one element shifts every later split point, regrouping the elements after
  it. For `f64` and `k = MAX / 4.001`:
  - With bounds `[-k, k]`, deleting the last element of a 32-element dataset changes the output of
    `make_sum(VectorDomain::new(AtomDomain::new_closed((-k, k))?), InsertDeleteDistance)` by
    `3.6e308`. Its `map(&1)` is `1.8e308`.
  - In the sized case, with 6 elements in `[-k', 2k']` and `k' = MAX / 3.001`, one deletion plus one
    insertion (`d_in = 2`) changes the output by `4/3` of the map.
- **How found:** While specifying the ordered sums, the derivation in the code comment did not
  account for saturation. An exhaustive search over clamped integer sums (`[-C, C]` in place of
  `[MIN, MAX]`) then found counterexamples for pairwise summation only. A test against OpenDP
  confirmed them, and `scripts/pairwise_ordered_sum_counterexample.py` reproduces them.
- **Impact:** The stability map, and so the privacy guarantee of any downstream mechanism,
  underestimates the change in the output. The worst example found is off by a factor of 2; the
  searches were small, so larger factors are not ruled out. It only happens when sums saturate,
  so values must be large: up to `size_limit` of them must sum to `MAX`. That is exactly when
  `make_sum` chooses this sum. Under `SymmetricDistance`, `make_sum` shuffles first, so the
  violation holds for a fraction of the orderings rather than all of them.
- **Fix:** Use sequential summation when saturating. The sequential saturating sum of integers is
  proved stable under insertion and deletion (the integer ordered sums), and the same search found
  no counterexample for sequential summation. Alternatively, keep pairwise summation with a
  sensitivity that accounts for regrouping.

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

### D4. The float sum relaxation relies on accuracy beyond the Proof Definitions

- **Where:** `rust/src/transformations/sum/float/mod.rs`, `SumRelaxation::error` for `Sequential<T>`
  and `Pairwise<T>`.
- **What:** Both bounds compute `2^-k` (`k = MANTISSA_BITS`) by dividing by
  `_2.inf_powi(k)`, which by its Proof Definition is only an *upper* bound on `2^k`. Dividing
  by an upper bound gives a *lower* bound, so the computed bound is only an upper bound because
  powers of two are computed exactly. The pairwise bound also computes `uk / (1 - uk)`, with
  `uk >= log2(n) / 2^k` rounded up and `1 - uk` rounded down. The Proof Definitions of `inf_log2`,
  `inf_div` and `neg_inf_sub` bound their results on one side only. They allow `inf_log2(n)` to
  return, say, `2^30` for `f32`. Then `1 - uk < 0`, and the relaxation is negative.
- **Why it is still sound:** The implementations round accurately, to within one unit in the last
  place. The Creusot proof assumes much less: each result is within half its magnitude plus
  `2^-10` of the exact value (`RealModel::rounds_close`), and `2^k` is exact. Removing either
  assumption makes the proof fail.
- **Impact:** None with the current implementations, but the relaxation's soundness silently
  depends on how accurate the arithmetic is.
- **Suggestion:** Compute `2^-k` exactly, or divide by a lower bound (`neg_inf_powi`). Also return
  `Err` unless the computed `1 - uk` is positive. With both changes the Proof Definitions alone
  suffice.

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
| A lemma (unit-valued logic function) called in a `proof_assert!` in program code is erased, so its conclusion is not instantiated. | Return `bool` with `#[ensures(result && conclusion)]`, and assert the call. |
| An impl method without a contract does not inherit its trait method's contract. | Restate the contract on the impl (trusted impls included). |
