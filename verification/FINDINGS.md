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
  it. For `f64`, through `make_sum(domain, InsertDeleteDistance)`, the shortest examples found are:
  - Unsized, bounds `[-k, 2k]` with `k = MAX / 4.001`: deleting the first element of the
    11-element `[2, -1, -1, 2, 2, 2, 0, -1, -1, -1, -1] * k` changes the output by `1.80e308`
    (`2k` to `-1.999k`). Its `map(&1)` is `1.35e308` (`~3k`), a factor of `1.333`.
  - Sized (10), bounds `[-k, k]` with `k = MAX / 2.001`: deleting the last element of
    `[-1, -1, 1, 1, 1, 1, -1, -1, -1, -1] * k` and inserting `k` at the front (`d_in = 2`) changes
    the output by `2.69e308` (`-2k` to `0.999k`). Its `map(&2)` is `1.80e308` (`~2k`), a factor of
    `1.4995`.

  The largest factor found is `1.999`: with bounds `[-k, k]` and `k = MAX / 4.001`, deleting the
  last element of a 32-element dataset. `make_sum` only accepts bounds with
  `max(|L|, U) <= 2^1023` (its overflow check rounds `max(|L|, U)` up to a power of two) and
  `U - L` is finite. The constructors themselves accept wider bounds, such as a 6-element sized
  example in `[-k, 2k]` with `k = MAX / 3.001`, off by `4/3`.
- **How found:** While specifying the ordered sums, the derivation in the code comment did not
  account for saturation. An exhaustive search over clamped integer sums (`[-C, C]` in place of
  `[MIN, MAX]`) then found counterexamples for pairwise summation only. A second exhaustive search,
  over integer multiples of `k` within `make_sum`'s limits on the bounds, found the short examples
  above. Nothing shorter exists on the grids searched: unsized with bounds `[-1, 1]`, `[-1, 2]` and
  `[-2, 3]`; sized with `[-1, 1]`, and up to 8 and 7 elements with `[-1, 2]` and `[-2, 3]`.
  A temporary test against OpenDP's `make_sum` confirmed them (the outputs and maps above), and
  `scripts/pairwise_ordered_sum_counterexample.py` reproduces them in Python.
- **Impact:** It only happens when sums saturate, so values must be large: up to `size_limit` of
  them must sum to `MAX`. That is exactly when `make_sum` chooses this sum. The impact depends on
  how the data's order is chosen:
  - **Broken: `make_sum` under `InsertDeleteDistance`, and direct calls to
    `make_(sized_)bounded_float_ordered_sum::<Pairwise<T>>`.** The caller's order is used as-is.
    The stability map, and so the privacy guarantee of any downstream mechanism, underestimates the
    change in the output. The worst example found is off by a factor of 2; the searches were
    small, so larger factors are not ruled out.
  - **Unproven, no counterexample: `make_sum` under `SymmetricDistance`.** `make_sum` shuffles
    first (`make_ordered_random`), so the output is random. Its justification chains the shuffle
    (symmetric distance `d` to insert-delete distance `d`) with the ordered sum's stability for
    every ordered pair, which is false, so the guarantee is not proved. But the property it needs
    appears to hold: stability of a randomized transformation means a coupling of the outputs on
    neighbouring datasets within the map (`W_inf <= map`), which suffices for noise calibrated to
    the map. On the F2 examples, the natural coupling (shuffle `x`, delete the same element)
    violates the map for 0.11% of orderings (11 elements), but the optimal coupling gives
    `W_inf = 0.67 x map` (11 elements) and `0.5 x map` (32 elements), and `Laplace(map / eps)` loses
    at most `0.64 eps` and `0.43 eps` (for `eps` in `{0.1, 1, 5}`). An exact search over every
    multiset of integer multiples of `k` found no neighbouring pair with `W_inf > map` or a Laplace
    loss above `eps`: unsized up to 48 values in `[-1, 1]`, 24 in `[-1, 2]` and 16 in `[-2, 2]`;
    sized up to 40 values in `[-1, 1]` and 20 in `[-1, 2]`, all at `make_sum`'s smallest accepted
    `MAX`; and at larger `MAX` (up to `6.001`) for up to 20-40 values
    (`scripts/pairwise_ordered_sum_shuffled.py`). This uses real arithmetic and assumes a uniform
    shuffle; the worst `W_inf` found is exactly the map, from pairs that never saturate, so there is
    no margin beyond the relaxation for rounding.
- **Fix:** Use sequential summation when saturating. The sequential saturating sum of integers is
  proved stable under insertion and deletion (the integer ordered sums), and the same search found
  no counterexample for sequential summation. Alternatively, keep pairwise summation with a
  sensitivity that accounts for regrouping.
- **Status:** Fixed on this branch in `make_sum`: its four ordered float branches use
  `Sequential<T>` (verified stable). The checked branches keep `Pairwise<T>`, which is verified.
  `transformations::sum::test::test_make_sum_float_saturating_is_stable` is the 32-element example
  above; it fails before the fix. `Pairwise<T>` is still the default `S` of the ordered sum
  constructors when called directly, and remains unstable there.

### F3. `make_clamp` on pairs fails depending on the data

- **Where:** `rust/src/transformations/clamp/mod.rs` (`make_clamp`), with the atom type `(f32, f32)`
  or `(f64, f64)`; `rust/src/traits/operations/mod.rs`, `impl ProductOrd for (T1, T2)`.
- **What:** `ProductOrd` is documented as "well-defined on types that are Ord on their non-null
  values", and `make_clamp`'s proof (`make_clamp.tex`) relies on this. But the pair impl is the
  componentwise (product) order, so two non-null pairs may be incomparable, and then `total_cmp`
  returns `Err`. `Bounds::new_closed` checks the bounds with `PartialOrd`, which on pairs is
  lexicographic. With a non-NaN `VectorDomain<AtomDomain<(f64, f64)>>`:
  - Bounds `((0, 10), (1, 0))` are accepted, as `(0, 10) < (1, 0)` lexicographically. The
    transformation returns `Ok([])` on the empty dataset and `Err` on every other dataset, because
    each row first compares the bounds themselves.
  - Bounds `((0, 0), (10, 10))` are fine, but the row `(-1, 20)` is incomparable with `(0, 0)`, so
    any dataset containing it gives `Err("unknown ordering ...")`, while `(1, 2)` gives `Ok`.
- **How found:** Specifying `ProductOrd` for the proof of `make_clamp`. The contract "`total_cmp`
  succeeds on non-null values" could not be proved for the pair impl, so the model records whether
  a type's order is total (`ProductOrd::total`), which is false for pairs. `make_clamp`'s success
  on every non-null dataset is then proved only for total orders. Confirmed by running both
  examples.
- **Impact:** A transformation whose function fails depending on the data. Whether it fails reveals
  whether some row is incomparable with the bounds, and the output is not in the output domain.
  Reachable only from Rust: the FFI dispatches `make_clamp` on numeric types only.
- **Fix:** Restrict `make_clamp` (and `ProductOrd`) to totally ordered types, or clamp pairs
  componentwise. Checking the bounds with `ProductOrd` at construction fixes the first example only.
- **Status:** Fixed on this branch.
  - `make_clamp` checks the bounds with `total_gt` at construction, so the first example is
    rejected when the transformation is built (`test_make_clamp_rejects_unordered_pair_bounds`).
  - `total_clamp` on pairs clamps each component separately. Wherever the old clamp succeeded, it
    gives the same result, and it also succeeds on rows that are not ordered with the bounds:
    `(-1, 20)` becomes `(0, 10)` (`test_make_clamp_pairs_componentwise`).
  - `make_clamp` is proved to succeed on every dataset of non-null rows, for every atom type.
  - `total_cmp`, `total_max` and `total_min` on pairs still fail on pairs that are not ordered
    componentwise, as documented on `ProductOrd`. No verified component relies on them for pairs.

### F4. `make_resize` is not stable from `InsertDeleteDistance` to `InsertDeleteDistance`

- **Where:** `rust/src/transformations/resize/mod.rs` (`make_resize`, now `resize_vec`), with
  `MI = MO = InsertDeleteDistance`. Reachable from Python and the FFI, which dispatch all four
  metric pairs.
- **What:** The function pads datasets of at most `size` rows and shuffles the result when the
  output metric is ordered, and truncates longer datasets, shuffling first only when the input
  metric is unordered. Under `InsertDeleteDistance` on both sides, a dataset of exactly `size`
  rows is therefore shuffled, while its neighbour with one more row is truncated without a
  shuffle. With `size = 3`, `x = [1, 2, 3]` and `y = [1, 2, 3, 1]` are at insert-delete distance
  1, `y` always maps to `[1, 2, 3]`, and `x` maps to each ordering of itself with probability 1/6.
  `[3, 2, 1]` is at insert-delete distance 4 from `[1, 2, 3]`, but `map(1) = 2`. Since one output is
  deterministic, no coupling of the outputs is within `map(1)`. In general the distance between a
  random ordering of `x` and `x` itself approaches `2 size` as `size` grows.
- **How found:** Reading the code to plan its proof, then confirmed by proof and by running it.
  The proof of the unchanged code (commit `2e2cc8a4`) showed the other three metric pairs stable,
  and `InsertDeleteDistance` to `InsertDeleteDistance` stable on every pair of datasets except a
  padded `x` and a truncated `y`. For that case `resize_id_id_unstable` proved the counterexample
  above, for any three distinct values.
- **Impact:** The transformation's stability claim is false. A downstream computation that depends
  on the order of the rows, calibrated to `map(d_in)` under `InsertDeleteDistance`, gets a privacy
  guarantee weaker than stated. Order-insensitive computations (counts, integer sums) are not
  affected, because the output multisets are the same.
- **Fix:** Shuffle the padded dataset only when the output metric is ordered and the input metric
  is not (`MO::ORDERED && !MI::ORDERED`). Under `InsertDeleteDistance` on both sides the function
  then pads at the end and truncates to a prefix, deterministically. This changes behavior only
  for `InsertDeleteDistance` to `InsertDeleteDistance`.
- **Status:** Fixed on this branch as above. All four metric pairs are proved stable with
  `map(d) = 2 d` (`resize_id_id_stable` for this one). `test_insert_delete_boundary_stability`
  (the counterexample, which failed before the fix) and `test_insert_delete_keeps_order` check it.

### F5. `make_impute_uniform_float` panics on infinite bounds, depending on the data

- **Where:** `rust/src/transformations/impute/mod.rs` (`make_impute_uniform_float`), for `f32` and
  `f64`. Reachable from Python and the FFI.
- **What:** The constructor rejects NaN bounds and `lower >= upper`, but not infinite bounds. The
  row function samples from `rand`'s `Uniform::from(lower..upper)`, whose constructor panics unless
  both bounds are finite. With bounds `(0, ∞)` the transformation is built, returns datasets without
  NaN unchanged, and panics on the first dataset with a NaN row.
- **How found:** Reading the code to plan its proof, then confirmed by proof and by running it. The
  sampler is specified with `rand`'s preconditions (finite bounds, `lower < upper`); after the
  constructor's checks, the bounds are proved non-NaN and ordered, and only their finiteness fails.
- **Impact:** Whether the transformation panics reveals whether the data contains a null. In a
  process that does not recover from panics, a data-dependent crash.
- **Fix:** Reject non-finite bounds when the transformation is built.
- **Status:** Fixed on this branch (`test_impute_uniform_rejects_infinite_bounds`). With the check,
  the transformation is proved to meet its contract and to be stable.

### F6. `make_impute_uniform_float` samples only part of very wide bounds

- **Where:** `rust/src/transformations/impute/mod.rs`, with finite bounds whose width
  `upper - lower` overflows, e.g. `(-f64::MAX, f64::MAX)`.
- **What:** `rand` 0.7's `UniformFloat::new` computes the width `upper - lower` (infinite here) and
  shrinks it until `lower + width * max_rand < upper`, ending at `f64::MAX`, so samples cover only
  `[lower, lower + MAX)`. With `(-MAX, MAX)`, 2000 imputed samples all lay in `[-MAX, 0)`. The
  documentation promises "uniformly distributed floats within `bounds`".
- **Impact:** None on privacy or on the output domain: the samples are finite and within the bounds,
  which is all the proof needs. The imputed distribution differs from the documented one.
- **Fix:** Reject bounds whose width is not finite, or document the restriction.
- **Status:** Not fixed (recorded only).

### F7. The threshold privacy maps understate δ by one point of mass

- **Where:** `rust/src/measurements/noise_threshold/distribution/laplace/mod.rs`,
  `NoiseThresholdPrivacyMap for ZExpFamily<1>` (`make_laplace_threshold`), and its proof
  `NoiseThresholdPrivacyMap_for_ZExpFamily1.tex`. The Gaussian map
  (`distribution/gaussian/mod.rs`, `make_gaussian_threshold`) has the same pattern (out of scope;
  confirmed by running it only).
- **What:** The function keeps a key when its noisy value is at least the threshold
  (`v + Z ≥ T`). A key present in only one of two neighbouring maps, with value at most `Δ∞`, is
  therefore released with probability up to `Pr[Z ≥ T - Δ∞]`, and an `(ε, δ)` guarantee needs
  `δ ≥ Pr[Z ≥ T - Δ∞]` (for one such key). The map computes `δ` from
  `conservative_{discrete,continuous}_laplacian_tail_to_alpha(scale, T - Δ∞)`, which bound
  `Pr[Z > T - Δ∞]`, and the proof treats `v + Z = T` as discarded (`Pr[c_j + Z_j ≤ T]`). For the
  discrete Laplace, `Pr[Z > d] = e^{-1/s} Pr[Z ≥ d]`, so `δ` is too small by a factor `e^{1/s}`
  (the continuous fallback `e^{-d/s}/2` is also below `Pr[Z ≥ d]`).
- **Confirmed:**
  - By proof (`verification/lean/OpenDPVerification/Threshold.lean`): the code's discrete tail
    formula `e^{-d/s} / (e^{1/s} + 1)` is exactly `Pr[Z > d]` (`discrete_bound_eq`), and both it and
    `e^{-d/s} / 2` are strictly below the release probability `Pr[Z ≥ d]`
    (`threshold_delta_too_small`).
  - By running it: with scale 1, threshold 3 and `d_in = (1, 1, 1)`, `{true: 1}` releases `true`
    with probability 0.099 (exact `Pr[Z ≥ 2]` = 0.0989; `{}` never releases it), but the map
    returns `δ = 0.036` (`Pr[Z > 2]`). Gaussian, scale 1, threshold 3: 0.059 against
    `δ = 0.023`.
- **Impact:** The `(ε, δ)` guarantee of `make_laplace_threshold` is wrong: the actual `δ` is up to
  `e^{1/scale}` times the reported one (2.7 times at scale 1). Reachable from Python and the FFI.
- **Status:** Fixed on this branch by making the release rule strict: a key is kept when its noisy
  value is strictly beyond the threshold (`v + Z > T`, or `< T` for a negative threshold), so it is
  released with probability `Pr[Z > T - v]`, which the existing `δ` bounds. The rule is shared, so
  this also changes (and fixes) `make_gaussian_threshold`, whose map also bounds `Pr[X > t]`. The
  Laplace privacy map is proved against the corrected mechanism theorem, and the Lean file shows
  the computed tail is exactly the new release probability (`releaseProbStrict_eq`,
  `discrete_bound_eq`). Tests: `test_laplace_threshold_delta_bounds_release`, and existing tests
  updated so that a value exactly at the threshold is not released.

### F8. The threshold mechanisms leak keys whose value is zero

- **Where:** the same function and privacy map; the input metric `L0PInfDistance`
  (`metrics/mod.rs`).
- **What:** The metric's Proof Definition reads a missing key as the additive identity: `{k: 0}` and
  `{}` are at distance `(0, 0, 0)`, and more generally a key with value 0 present in only one map
  does not count towards `l0`. The privacy map returns `(0, 0)` when the sensitivity is zero, and
  otherwise counts only `l0` unstable keys. But the mechanism releases a key with value 0 when
  `Z ≥ T`, with positive probability, and never releases a missing key.
- **Confirmed:**
  - By proof: a key with value 0 is released with positive probability (`zero_key_released`).
  - By running it: with scale 1 and threshold 1, `map((0, 0, 0)) = (0, 0)`, but `{true: 0}`
    releases `true` 27% of the time and `{}` never.
- **Impact:** Neighbouring maps that differ in keys with value 0 are distinguished with probability
  not covered by the privacy map (at distance 0, any positive probability violates `(0, 0)`). Maps
  from `make_count_by` hold only observed keys with positive counts, so the common pipeline is not
  affected; maps built otherwise (or after transformations that can produce zeros) are.
- **Status:** Fixed on this branch: keys with value 0 are dropped before noise is added, so the
  mechanism treats them as the metric does (as missing keys). For float maps, values that round
  to 0 are dropped in the same way. Test: `test_laplace_threshold_drops_zero_keys`. The drop is
  in the trusted noise function (`noise_threshold_function`), so this test, not the proof, guards
  it.

### F9. `make_np_clamp` outputs can lie outside the norm ball when `origin` is far from zero

`make_np_clamp` (`python/src/opendp/extras/numpy/_make_np_clamp/__init__.py`) is pure Python and
numpy. F9-F17 concern it. F9-F14 are proved in `verification/lean/OpenDPVerification/NpClamp.lean`
against a hand transcription of `_function` (`clampV0`) and a model of the numpy operations it uses
(`TRUST.md`). All of F9-F17 reproduce with numpy 2.5 and the released opendp package
(`verification/scripts/np_clamp_counterexamples.py`). The constructor needs only the `contrib`
feature, not `idealized-numerics`, so its claims are meant to hold for floats. All are fixed on
this branch. The fixed code is proved in the same file (`clamp`). Each fix has a regression test in
`python/test/extras/test_clamp_numpy.py`, and each test fails on the code before the fixes.

- **What:** The function clamps `arg = x - origin` and returns `arg + origin`. That addition rounds,
  so the output can be farther from `origin` than `norm`: by up to half the float spacing at
  `origin`, per coordinate.
- **Confirmed:**
  - By proof (`origin_rounding`): with `origin = [2^56]`, `norm = 12` and `p = 2`, the row
    `[2^56 + 48]` is clamped to `[2^56 + 12]`, which rounds to `[2^56 + 16]` (floats near `2^56` are
    16 apart). The output fails the output domain's own check.
  - By running it: the output is 16 from the origin and is not a member of the output domain.
- **Impact:** The output domain's norm bound, which downstream sensitivities use, is exceeded by up
  to `sqrt(d)` times half the spacing at `|origin|`. This is negligible unless `|origin|` is about
  `2^52 · norm` or more. PCA passes a DP estimate of the mean as `origin`. Its consumers
  (`make_np_sum`, PCA) require `idealized-numerics` anyway.
- **Status:** Fixed on this branch. After adding `origin` back, the function recomputes each row's
  norm with the domain's check, and replaces rows outside the ball by `origin`. Proved:
  `clamp_member`, every output row passes the domain's check, for any origin. Test:
  `test_clamp_origin_rounding`.

### F10. `make_np_clamp` misses large rows when the L2 norm underflows

- **What:** `np.linalg.norm(x, ord=2)` squares each element without rescaling, so squares below
  about `2^-1075` round to 0. With a bound below about `1e-154`, a row can be above the bound but
  have computed norm 0. The row is then output unchanged, and the domain's check (the same
  computation) accepts it.
- **Confirmed:** by proof (`l2_underflow`: `norm = 2^-600`, row `[2^-565, 0]`), and by running it.
- **Impact:** Only for absurdly small bounds (below about `1e-154`).
- **Status:** Fixed on this branch: `norm` must be at least `2^-458` for `float64` data (`2^-39`
  for `float32`).
  - Proved (`l2_true_norm`, `clamp_true_norm`, origin zero): a row with computed L2 norm `c` has
    true squared norm at most `((c + η)² + n η) / (1 - 2^-p)^(n+2)`, with `η` half the smallest
    subnormal.
  - The minimum norm makes `n η ≤ (2^-p norm)²` and `η ≤ 2^-p norm` for `n ≤ 2^p` columns
    (`min_norm_f64`, `min_norm_f32`).
  - The excess is then a relative rounding error, about `(n/2 + 2) 2^-p` (`slack_le`).
  - For `p = 1` there is no underflow: the true norm is at most `c / (1 - 2^-p)^(n-1)`
    (`l1_true_norm`).
  - Test: `test_clamp_rejects_tiny_norm`.

### F11. `make_np_clamp` can loop forever, depending on the data

- **What:** The loop divides each row by `max(norm(row) / norm, 1)` until every computed norm is
  within the bound. Dividing a tiny element by a factor close to 1 can round back to the same
  element. If every element of a row above the bound is like that, the loop never ends.
- **Confirmed:**
  - By proof, with `p = 1`:
    - `nonterm_subnormal`: `norm` is 3 times the smallest subnormal, and the row is four smallest
      subnormals.
    - `nonterm_normal`: `norm = 2^-1022`, the smallest normal float. The row has three subnormal
      elements whose sum is one spacing above the bound. The factor is `1 + 2^-52`, and each
      element rounds back to itself.
  - By running it: neither call returns.
- **What is proved instead** (`clamp_terminates`): the loop terminates when `norm` is a normal
  float, and for `p = 1` when also `norm ≥ d · 2^-1022` for `d ≤ 2^53` columns. Then each pass
  shrinks some element of each row above the bound by at least one representable step. The two
  counterexamples show neither condition can be dropped. Termination for `p = 2` with a subnormal
  bound is neither proved nor refuted.
- **Impact:** A data-dependent hang (availability, and a timing channel), only for bounds below
  `d · 2^-1022`.
- **Status:** Fixed on this branch by the same minimum norm (F10).
  - `2^-458` is at least `2^p · 2^-1022` (`2^-39` is at least `2^24 · 2^-126` for `float32`). So
    the hypotheses of `clamp_terminates` hold for rows of at most `2^p` values (`TermHyp.of_min`,
    `min_norm_f64`, `min_norm_f32`).
  - `float32` arrays with more than `2^24` columns are not covered.
  - Test: `test_clamp_rejects_tiny_norm`.

### F12. `make_np_clamp` with `norm` equal to the largest float accepts rows of infinite norm

- **What:** `get_norm` applies `np.nan_to_num`, which turns an infinite norm into the largest
  finite float. With `norm` equal to that float, a row whose norm overflows is treated as within
  the bound and output unchanged, but the output domain's check computes the norm `inf`.
- **Confirmed:** by proof (`max_bound_overflow`, `p = 1`, row `[MAX, MAX]`, for any format), and by
  running it.
- **Impact:** Only for `norm = MAX`, where the downstream sensitivity is useless anyway.
- **Status:** Fixed on this branch by the recheck of F9: the row's norm is recomputed without
  `nan_to_num`, so it is `inf`, and the row is replaced by `origin`. Proved: `clamp_member`. Test:
  `test_clamp_max_norm`.

### F13. `make_np_clamp` raises on the empty dataset

- **What:** `current_norm.max()` raises `ValueError` on an array with no rows. The function
  therefore raises on the empty dataset, and returns on its neighbours.
- **Confirmed:** by proof, in the model (`empty_error`, where the model encodes numpy's behavior
  on empty arrays), and by running it.
- **Impact:** Whether the dataset is empty is revealed exactly, through the exception, for domains
  without a known size. The stability map `d_in ↦ d_in` assumes the function returns on both
  neighbours.
- **Status:** Fixed on this branch.
  - The loop condition is `(current_norm > norm).any()`, which is false on an empty array, so the
    empty dataset is clamped to itself. Proved: `clamp_empty`, and `clamp_terminates` now holds for
    every dataset.
  - The domain's check used `.max()` too, so empty arrays were not members. It now uses `.any()`.
  - Test: `test_clamp_empty`.

### F14. `make_np_clamp` keeps `cardinalities` that clamping can invalidate

- **What:** The output domain copies the input domain's descriptor, including `cardinalities` (the
  maximum number of distinct values per column). Clamping scales each row by its own factor, so
  equal values in a column can become different.
- **Confirmed:** by proof (`cardinalities`: with `p = 1` and `norm = 1`,
  `[[2, 0], [2, 2]]` becomes `[[1, 0], [0.5, 0.5]]`, so the first column goes from one distinct value
  to two), and by running it: the output is not a member of the output domain.
- **Impact:** No code reads `cardinalities` from a numpy array domain today. A future consumer
  would rely on a false bound.
- **Status:** Fixed on this branch: the output domain has no `cardinalities`. Test:
  `test_clamp_drops_cardinalities`.

### F15. `make_np_clamp` clamps rows differently depending on the array's memory layout

- **What:** numpy sums the rows of a Fortran-ordered array in a different order than those of a
  C-ordered one. The computed norms, and so the clamped rows, can differ in the last bits.
  The same dataset in two layouts can therefore give outputs at symmetric distance greater than
  0. More generally, `d_out ≤ d_in` needs the summation order of a row to depend only on the row.
- **Confirmed:** by running it only: a `4 × 16` normal sample (seed 1) has one row clamped
  differently in the two layouts (by `1.1e-16`). For C-ordered arrays, row norms were the same
  whatever the number of rows, for every shape tried.
- **What is proved instead** (`clamp_map`, `clamp_stable`): when the summation order depends only
  on the row length (as for C-ordered arrays), each output row depends only on its input row,
  despite the loop over the whole array, and `d_out ≤ d_in`.
- **Impact:** Differences are at the level of rounding, and arise only if neighbouring datasets
  could have different layouts.
- **Status:** Fixed on this branch: the function converts its working array with
  `np.ascontiguousarray`. The fix relies on numpy's current behaviour. The model assumes it (a
  summation order per row length), and `clamp_map` and `clamp_stable` hold under that assumption.
  Test: `test_clamp_layout`.

### F16. `make_np_clamp` on `float32` data clamps to the `float32` rounding of `norm`

- **What:** With `float32` arrays, numpy 2 converts the Python float `norm` to `float32` in
  `current_norm.max() > norm` and `current_norm / norm`. `float32(norm)` can exceed `norm`.
- **Confirmed:** by running it only: with `norm = 0.1` and `float32` data, the rows of the output
  have exact norms `0.1000000015` and `0.10000000000000005`, both above `0.1`. The output fails the
  output domain's own check.
- **Impact:** The bound is exceeded by up to a relative `2^-24`, for ordinary parameters.
  `make_np_sum` and PCA, which use the bound, require `idealized-numerics`.
- **Status:** Fixed on this branch.
  - The function clamps to `norm_T`, the largest value of the data type that is at most `norm`
    (`float(norm_T) > norm` is compared exactly).
  - The domain's check computes in the precision of the array, and compares with `norm` exactly
    (as `float64`): numpy would otherwise round `norm` to `float32`.
  - In the model, the bound is `norm_T`, and passing the check with `norm_T ≤ norm` implies passing
    it with `norm`.
  - Test: `test_clamp_f32`.

### F17. `make_np_clamp` changes the data type of its output

- **What:** With `float32` data and an `origin` array (`float64`), `arg - origin` promotes the
  array to `float64`. With integer data, the division produces floats. In both cases the output
  is a `float64` array, but the output domain keeps the input's type.
- **Confirmed:** by running it only:
  - `float32` data with `origin=[0.5, 0.5]` gives a `float64` output, which is not a member of the
    output domain;
  - `int32` data gives `float64` values such as `[[0.6, 0.8]]`.
- **Impact:** Outputs fail the output domain's type check, so the domain's claim is false. Downstream
  constructors see an unexpected type.
- **Status:** Fixed on this branch:
  - the input domain must have float elements;
  - `origin` is converted to the data type (and checked to be finite after the conversion), so the
    arithmetic stays in it. The output domain records the converted origin.
  - Test: `test_clamp_dtype`.

### F18. `make_np_clamp` takes up to ~2^52 passes when `norm` is near the largest float

- **What:** When a row's computed norm overflows, `nan_to_num` makes it the largest float, so the
  row's factor is `max / norm_T`. For `norm` near the largest float this factor is barely above 1,
  and each pass of the loop shrinks the row by about that factor. For `p = 2` the norm overflows as
  soon as the squares do, i.e. for elements above about `1.3e154`. The number of passes is about
  `log(excess) / log(max / norm_T)`.
- **Confirmed:** by running it only (the loop of `_function` in numpy 2.5.4):
  - `norm = nextafter(max, 0)`, `p = 2`, row `[1e200, 1e200]`: still looping after 2.3 million
    passes (20 s); the estimate is ~10^17 passes;
  - `norm = nextafter(max, 0)`, `p = 1`, row `[max, max]`: likewise;
  - `norm = 0.995 * max`, `p = 2`, a row of 300 values around `1e270`: 52,977 passes. The
    conformance tests found this case: the Lean model ran out of its fuel of 10,000 passes.
- **Not in conflict with the proofs:** `clamp_terminates` proves termination, but its bound counts
  steps of the smallest subnormal and is astronomically large.
- **Impact:** For such norms, the transformation effectively never returns on some datasets
  (denial of service). The number of passes, and so the running time, depends on the data.
- **Status:** Open. One option is to divide rows whose norm overflows by a power of two, which is
  exact, before computing the factor.

### F19. `fill_null` changes the column's type, but the output domain keeps the data's

- **What:** Polars casts `data.fill_null(fill)` to the supertype of the data's and the fill's
  types. `make_expr_fill_null` copies the data's domain to the output, type included, and only
  rejects categorical data and nullable fills.
- **Confirmed:** by running it only (Polars 0.52): on an `i32` column, the fills `1.5`, `2^40`,
  `"a"` and an `f64` column give `Float64`, `Int64`, `String` and `Float64` columns, which the
  output domain (`i32`) rejects (its member check errors). Test:
  `test_fill_null_keeps_dtype`.
- **Impact:** Constructors downstream choose their algorithm and sensitivity from the domain's
  type, for example integer arithmetic for an `i32` sum, while Polars computes on the supertype.
  No privacy violation has been shown.
- **Status:** Fixed on this branch: the constructor rejects a fill whose type is not the data's. A
  numeric scalar literal that the data's type represents exactly is first converted to it (so
  `fill_null(0)` and `fill_null(0.0)` still work on integer columns, as Polars treats Python
  literals). `dp.quantile`, which filled nulls with the median of the candidates as an `f64`, now
  converts it to the data's type.

### F20. `fill_null` claims no NaN when the fill can be NaN

- **What:** The output domain keeps the data's NaN flag. A fill that can be NaN (a NaN literal,
  or a column whose domain allows NaN) puts NaN into a column the domain says has none. `fill_nan`
  checks this (`fill_can_be_nan`); `fill_null` does not.
- **Confirmed:**
  - by running it: `col("x").fill_null(lit(NaN))` and `col("x").fill_null(col("f"))` on a
    non-NaN `f64` column give NaN, and the output domain's member check returns false. Test:
    `test_fill_null_nan`;
  - in Lean, on the model (`fill_nan_counterexample`). `fill_member` proves the claim holds when
    every fill value satisfies the data's predicate.
- **Impact:** see F21.
- **Status:** Fixed on this branch: the output's NaN flag is the data's or the fill's. Proved
  sound on the model (`fill_member_fixed`, `fill_noNaN_fixed`).

### F21. A null row changes a released sum by up to `n` (privacy violation)

- **What:** Through F20, `col.fill_nan(0.0).fill_null(NaN)` has a domain without NaN, so `clip`,
  `sum` and `.dp.noise()` accept it with sensitivity 1 (bounds `[0, 1]`). A single null row makes
  the sum NaN, and the noise mechanism rounds NaN to 0 before adding noise (`discretize_vec`, whose
  contract excludes NaN). Adding one row moves the value the noise is added to from `n` to 0.
- **Confirmed:**
  - in Lean: `null_leak` (any binary format, any summation order) and `null_leak_f64`: `n` rows of
    `1.0` give `n`, with one null row added (symmetric distance 1) they give 0;
  - by running it against the released package (opendp 0.16.0, Polars 1.36.1), at `ε = 1`: 1000
    rows of `1.0` release about 1000, and the same rows plus one null release about 0
    (`verification/scripts/fill_null_counterexamples.py`).
- **Impact:** A privacy violation: one release distinguishes neighbouring datasets almost
  certainly. The privacy loss is about `n / b` for noise scale `b`, not the claimed `1 / b`. It needs
  only a NaN fill, which an analyst may choose by mistake.
- **Status:** Fixed on this branch by the fix of F20: `sum` rejects the query ("input data (x)
  might contain nans"). Separately, `discretize_vec` maps NaN to 0 silently; it could instead
  return an error, as defence in depth.

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

### D5. The discrete Laplace mass is documented with the wrong sign

- **Where:** the Proof Definition of `ZExpFamily` (`rust/src/measurements/noise/mod.rs`), the
  docs of `sample_discrete_laplace` (`traits/samplers/cks20/mod.rs`) and of
  `conservative_discrete_laplacian_tail_to_alpha` (`accuracy/tail_bounds/mod.rs`), and the proof
  `NoisePrivacyMap_for_ZExpFamily1.tex`.
- **What:** The mass is given as `(e^{-1/s} - 1) / (e^{-1/s} + 1) e^{-|x|/s}`, which is negative
  for every `s > 0`. The correct constant is `(1 - e^{-1/s}) / (1 + e^{-1/s})`, as in
  `sample_discrete_laplace.tex` and `discrete_laplacian_scale_to_accuracy.tex`; the Lean proof
  checks that it sums to 1.
- **Why it is still sound:** the constant cancels in the privacy proof, and the sampler's proof
  uses the correct one. Only the documented definition is wrong.
- **Fix (on the branch):** the four occurrences are corrected.

### D6. `make_impute_uniform_float` passes a random row function to `make_row_by_row`

- **Where:** `rust/src/transformations/impute/mod.rs`; the proof of `make_row_by_row`
  (`transformations/manipulation/make_row_by_row.tex`).
- **What:** `make_row_by_row`'s proof requires of the caller that "`row_function` has no
  side-effects", and its stability argument maps each row by a function. The imputer's row
  function draws randomness, so the cited proof does not cover it, and `make_impute_uniform_float`
  has no proof of its own.
- **Why it is still sound:** The rows of the input are imputed independently. Coupling the samples
  of the rows that two neighbouring datasets share, and sampling the other rows freely, gives
  outputs within the same distance. The proof here states this for row-by-row relations
  (`EventModel::close_rel`, for all four event-level metrics) and applies it to the imputer.
- **Suggestion:** State `make_row_by_row`'s precondition as "independent per row" rather than "no
  side-effects", or give the imputer its own proof.

## Tool limitations (Creusot v0.14.0)

| Limitation | Workaround |
| --- | --- |
| Traits whose associated types refer back to themselves are rejected. | Declare them in `#[trusted]` modules. |
| Every `PartialEq` type needs a `DeepModel`; floats cannot have a sound one. | Derived/hand-written models; opaque models for carriers; trust generic float comparisons. |
| `dyn Fn` cannot be called or cloned in verified code. | Ghost models with trusted `new`/`eval`. |
| Float-to-float and int-to-float casts are unsupported. | Trust the code (casts module, float sums' overflow checks). |
| `Result::map` / `and_then` with closures defeat closure contract inference. | Use `?` instead. |
| Generic `Clone::clone` has no contract. | Avoid cloning `Copy` values; for `Number`s, a trusted lemma that `clone` is the identity (`number_clone`). |
| Calls to `std` functions without specifications (`format!`, backtraces) are unprovable. | Trusted constructors (e.g. `err!` under Creusot). |
| Crash (`unreachable!`) in the resolve backend on `dyn Any` types. | Not reported yet; avoided by trusting the code involved. |
| Unit-valued lemmas called under quantifiers (`forall<x> { lemma(x); p(x) }`) are erased, so they rarely apply. | Return `bool` with `#[ensures(result && conclusion)]` and assert `forall<x> h(x) ==> lemma(x)`, with `#[trigger(..)]` on terms the goal contains. |
| Large conjunctive predicates time out as one goal. | Mark them `inline` so they are split. |
| A lemma (unit-valued logic function) called in a `proof_assert!` in program code is erased, so its conclusion is not instantiated. | Return `bool` with `#[ensures(result && conclusion)]`, and assert the call. |
| An impl method without a contract does not inherit its trait method's contract. | Restate the contract on the impl (trusted impls included). |
| Laws (`#[logic(law)]`) cannot have generic parameters, and were not available as axioms in a trait's default method (`total_clamp`). | Bool-valued lemma methods (`ProductOrd::ple_refl`, `EventModel::close_map`) that every impl proves, called explicitly. |
| A method of an impl that calls a generic function (or a default method) using the same impl is rejected as possible recursion. | Expand the shared code with a macro inside each impl (`clamp_by_cmp_body!`). |
| Constants of foreign types (`RBig::ONE`, `UBig::ZERO`) are translated through their bodies, which call unspecified functions, so any goal using them is unprovable (in code or in specifications). | Use conversions with specifications (`RBig::from(1usize)`), or `sign()` instead of comparing with `RBig::ZERO`. |
| Float literals in specifications crash the translation ("Unsupported literal"). | A trusted helper returning the literal, with its value in the contract (`zero_loss`); constants such as `f64::INFINITY` work. |
| `std`'s `vec!` expands to code Creusot cannot translate (the closure's body becomes `false`). | Import creusot-std's `vec!` under `cfg(creusot)`. |
| Closures passed to `Function`/`StabilityMap`/`PrivacyMap` whose bodies use `map_err` or several early returns: their inferred contracts were too hard to use. | Move the body into a named function with an explicit contract (`discretized_distance`, `laplace_loss`, `to_rbig`). Likewise, iterator chains (`iter().map().collect()`) become indexed loops. |
| Derived `Clone` impls in trusted modules carry no contract. | Hand-write the clone, with a (trusted) contract (`AtomDomain`, `VectorDomain`). |
| A lemma used as a term in a contract (`ensures(singleton_valid(t))`) tells callers nothing, as its conclusion depends on its preconditions. | State the conclusion (`ensures(t_valid(t))`), and apply the lemma in the body. |
| why3find sometimes reports a failed assertion at the span of the whole function. | Run why3 with `split_vc` on the `.coma` file to locate the goal. |
| A `match` or `?` inside `x *= match { ... }` leaves `&mut` type invariants that time out. | Compute the right-hand side first. |
| The inferred precondition of a closure includes the type invariants of its arguments. | State function preconditions for values satisfying `inv(x)`. |
| Contracts written in a `#[trusted]` module are assumed without warning (by design), which is easy to miss when adding contracts to existing code: the new `ProductOrd` contracts were at first assumed, and a mutation check exposed it. | Untrust modules whose contracts the proofs rely on, and trust their other items individually. |
| `inline` predicates are expanded in program goals but not in lemma specifications, so a lemma about `contract(t)` does not match a hypothesis that `contract(t)` holds, unless the solver re-folds it (it often cannot after `?`). | Bind the `Result` and assert `forall<t> r == Ok(t) ==> stable(t)` directly; or use a non-`inline` alias of the contract. |
| Using `Seq::permutation_of` anywhere in a function's context (e.g. through a callee's contract) slowed unrelated real-arithmetic goals until they timed out. | Keep the definition of `reorders` visible only in its module, and reveal it with a lemma where needed. |
| Goals mentioning a constant (`DEFAULT_SIZE_LIMIT`) in both a hypothesis and a lemma failed to match, where the same goals with a variable succeeded. | Pass the constant as a parameter to the lemmas and instantiate it at the call site. |
