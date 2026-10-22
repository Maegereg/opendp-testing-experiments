# Formal verification of OpenDP (proof of concept)

Machine-checked verification of selected OpenDP components with
[Creusot](https://github.com/creusot-rs/creusot), a deductive verifier for Rust, and
[Lean 4](https://lean-lang.org) with Mathlib for floating-point arguments that need a model of rounding.

- [`TRUST.md`](TRUST.md): everything the proofs assume rather than prove.
- [`FINDINGS.md`](FINDINGS.md): bugs and other issues found along the way.

## Running

Requirements:

- Creusot v0.14.0 (`cargo creusot`), installed per its README.
- OpenDP's fork of `creusot-std`, which adds models for `dashu` numbers
  (branch `opendp-dashu` of a Creusot checkout).

```sh
export CREUSOT_STD_PATH=/path/to/creusot/creusot-std
# the verified components
tools/creusot.sh 'transformations::sum::*' 'transformations::count::*' \
  'transformations::clamp::*' 'transformations::manipulation::*' \
  'transformations::scalar_to_vector::*' 'transformations::cast_metric::*' \
  'combinators::chain::*' 'measurements::noise::*' \
  'verification::*' 'traits::*' 'domains::*' \
  'core::impl_Function_TI_TO_2::*' 'core::impl_StabilityMap_MI_MO_1::*' \
  'core::impl_Measurement_DI_MI_MO_TO::new'
tools/creusot.sh 'transformations::sum::int::checked::*'   # one module
```

The last three filters select `Function::make_chain`, `StabilityMap::make_chain` and
`Measurement::new` (Creusot numbers impl blocks). `'core::*'` also reports six failures in `Debug` impls and `invoke`, which are outside
the verified components, as does a run without a filter (plus `PartialEq` for metrics).

Lean (`verification/lean`, Mathlib v4.35.0, toolchain pinned by `lean-toolchain`):

```sh
cd verification/lean
lake exe cache get   # download prebuilt Mathlib
lake build           # check all proofs
```

Normal builds are unaffected: all annotations are behind `cfg(creusot)`, and `creusot-std` is
only a dependency under `cfg(creusot)`.

## Approach

- **Trust by default.** Creusot translates every function body in the crate, so modules
  outside the component under verification are marked `#[trusted]` under Creusot. Trusted code
  is not assumed correct, only skipped; its *contracts*, where it has any, are assumed (see
  `TRUST.md`).
- **Numbers are modeled by reals.** The contracts of the arithmetic traits (`inf_add`, `inf_cast`, ...)
  restate their documented Proof Definitions over the reals, via `RealModel::real`.
  Integer implementations are verified against them; float implementations are trusted.
- **Type-erased closures carry ghost models.** `Function` and `StabilityMap` wrap
  `Arc<dyn Fn>`, so their constructors record the wrapped closure's contract in a ghost model
  (`pre`, `post`), which `eval` replays.
- **Datasets are multisets.** `verification::dataset` models datasets by their real values and
  defines the symmetric distance by witnesses: `x` and `y` are within `d` if they share a common
  sub-multiset and differ by extra elements of total size at most `d`.
- **Stability is a theorem per constructor.** Each verified constructor has a contract, checked
  against its implementation, and a lemma deriving stability from that contract.
- **Mutation checks.** Each milestone is checked by injecting plausible bugs (e.g. halving the
  sensitivity, removing an overflow check) and confirming that verification fails.

## Status: `make_sum`

| Constructor | Status |
| --- | --- |
| `make_sized_bounded_int_checked_sum` | Verified: contract, function defined on the domain, stability theorem. |
| `make_(sized_)bounded_int_monotonic_sum` | Verified: contracts and stability theorems (sized and unsized). |
| `make_(sized_)bounded_int_ordered_sum` | Verified: contracts and stability theorems (sized and unsized), under the insert-delete distance. |
| `make_(sized_)bounded_int_split_sum` | Verified: contracts and stability theorems (sized and unsized). |
| `make_(sized_)bounded_float_checked_sum` | Verified: contracts and stability theorems (sized; unsized for datasets of at most `size_limit` values). Error bound computation verified; summation error bounds cited; overflow check proved in Lean. |
| `make_(sized_)bounded_float_ordered_sum` | `Sequential`: verified, contracts and stability theorems (sized; unsized for datasets of at most `size_limit` values), with the rounding error bound proved in Lean. `Pairwise`: contracts verified; **not stable** (`FINDINGS.md` F2). |
| `make_sum` (dispatch) | Verified, after switching its saturating float branches to `Sequential` (F2): every branch returns a stable transformation, for all 14 types and both metrics. Under `SymmetricDistance`, the shuffled float branches are stable up to a matching of the shuffles, which is cited for uniform shuffles. |

### `make_sized_bounded_int_checked_sum`

Proved (`rust/src/transformations/sum/int/checked/proof.rs`), for every integer type `T`:

1. The constructor meets its contract: on success, the input domain is vectors of `size`
   elements within `bounds` (with `lower <= upper`); some representable value bounds
   `size * max(|lower|, upper)`; the function returns the exact sum of any dataset whose prefix
   sums are representable; and the stability map returns at least `(d_in / 2) * (upper - lower)`.
2. On every dataset in the input domain, the function can be evaluated, does not fail, and
   returns the exact sum (no overflow).
3. Stability: on any two datasets in the input domain within symmetric distance `d_in`,
   `|f(x) - f(y)| <= map(d_in)`.

Mutation checks: underestimating the sensitivity (`d_in / 3`), removing the overflow check, or
claiming a tighter bound each make verification fail.

Code changes needed (behavior unchanged): the function calls `int_sum` (a trusted wrapper of
`iter().sum()`), the stability map uses `?` instead of `and_then`, and `bounds` is no longer
cloned (it is `Copy`).

### `make_bounded_int_monotonic_sum`, `make_sized_bounded_int_monotonic_sum`

Proved (`rust/src/transformations/sum/int/monotonic/proof.rs`): the constructors meet their
contracts (bounds share a sign; the function returns the saturating sum; the map returns at least
`d_in * max(|lower|, upper)`, resp. `(d_in / 2) * (upper - lower)`), and both are stable. The
saturating sum of same-sign elements is the clamped exact sum, and clamping is 1-Lipschitz.

Mutation checks: removing the sign check, dropping sign agreement from the contract (the
stability proof then fails, as order-dependent saturation breaks symmetric-distance stability),
and `d_in / 3` each make verification fail.

Code changes (behavior unchanged): the saturating fold is the `saturating_sum` helper (an
index loop, verified), `T::zero()` is the trusted `int_zero` wrapper, `?` replaces `and_then`.

### `make_bounded_int_split_sum`, `make_sized_bounded_int_split_sum`

Proved (`rust/src/transformations/sum/int/split/proof.rs`): the function is
`clamp(clamp(N) + clamp(P))`, where `N` and `P` are the exact sums of the negative and positive
parts, so the output moves by at most `|ΔN| + |ΔP|`. Under the symmetric distance this is at most
`d_in * max(|lower|, upper)` (unsized), resp. `(d_in / 2) * (upper - lower)` (sized, by the
identity `min(v, 0) + max(v, 0) = v` applied to the bounds).

Mutation checks: `d_in / 3`, and summing signed integers with a single saturating fold (which is
order-dependent) each make verification fail.

Code changes (behavior unchanged): both `SplitSatSum` impls call the verified
`split_saturating_sum` loop (for unsigned integers the negative sum is always zero), and
`SplitSatSum` requires `Integer`, which all its implementors are.

### `make_bounded_int_ordered_sum`, `make_sized_bounded_int_ordered_sum`

Proved (`rust/src/transformations/sum/int/ordered/proof.rs`, `rust/src/verification/ordered.rs`):
the function is the left-to-right saturating sum, with elements of either sign. The
insert-delete distance is modeled by a common subsequence `z` of `x` and `y`, with deleted
elements `dx` and `dy`. Deleting `dx` moves the saturating sum by between the sums of the negative
and positive parts of `dx` (each deletion of `e` moves a clamped value by between `min(e, 0)` and
`max(e, 0)`, and each kept element preserves that interval). This gives `d_in * max(|lower|, upper)`
(unsized), and with equal sizes `(d_in / 2) * (upper - lower)`: directly when
`lower <= 0 <= upper`, and via the clamped exact sum when the bounds share a sign.

A brute-force search over small types first found no counterexample to the sized map, whose
justification is less obvious than the others (saturation is order-dependent).

Mutation checks: `d_in / 3`, and a map of `d_in * upper` (ignoring `|lower|`), each make
verification fail.

### `make_bounded_float_checked_sum`, `make_sized_bounded_float_checked_sum`

Proved (`rust/src/transformations/sum/float/{proof.rs,checked/proof.rs}`), for `S` =
`Sequential<T>` or `Pairwise<T>` and every float type `T`:

1. **The relaxation is large enough.** `S::error(size, lower, upper)` returns `e` bounding the
   rounding error of summing `size` values within the bounds (`SumRelaxation::error_bound`), and
   `relaxation` returns at least `2 e`. The bounds are the cited ones: `(n - 1) u sum |x_i|`
   sequentially, and `gamma(ceil(log2 n)) sum |x_i|` pairwise, with `u = 2^-(MANTISSA_BITS + 1)`
   the unit roundoff and `gamma(h) = h u / (1 - h u)`. The code instead uses
   `n^2 2^-MANTISSA_BITS max(|L|, U)` and `gamma'(log2 n) n max(|L|, U)`, with
   `gamma'(k) = k 2^-MANTISSA_BITS / (1 - k 2^-MANTISSA_BITS)`. The pairwise proof uses
   `ceil(log2 n) <= 2 log2 n` (D1) and needs accurate rounding (D4).
2. **The constructors meet their contracts:** inputs within the bounds; summing at most `size`
   (resp. `size_limit`) values within them does not overflow, by `can_float_sum_overflow`; the
   function returns the float sum (unsized: of datasets of at most `size_limit` values); the
   stability map returns at least `(d_in / 2) (U - L) + 2 e` (sized) or
   `d_in max(|L|, U) + 2 e` (unsized).
3. **Stability:** the float sums of two datasets within symmetric distance `d_in` differ by at
   most `|f(x) - sum(x)| + |sum(x) - sum(y)| + |sum(y) - f(y)| <= e + d_in * sensitivity + e`.
   For the unsized sum, this covers datasets of at most `size_limit` values. Larger ones are
   shuffled and truncated, and the function is then randomized: its stability needs a coupling
   argument, not attempted here.

Floats are modeled by the real numbers they represent, which are left opaque (and by whether
they are finite). Float addition is never modeled directly. The proof relies on:

- the summation error bounds, cited (Rump 2012 and Jeannerod & Rump 2013 for sequential
  summation, valid for any `n`; Higham 2002, §4.2 for pairwise summation);
- the overflow check, proved in Lean (below);
- the outward-rounding contracts of the arithmetic, plus accuracy (D4).

Mutation checks: each of the following makes verification fail:
- `d_in / 3` in the sized map;
- a relaxation of `e` instead of `2 e`;
- no overflow check;
- `n` instead of `n^2` in the sequential bound;
- no factor `n` in the pairwise bound;
- the unsized sensitivity `U - L` instead of `max(U - L, |L|, U)`.

Weakening the accuracy of `neg_inf_sub` or `inf_log2` to their Proof Definitions, or `2^k` to an
upper bound, also makes it fail (D4).

Code changes (behavior unchanged):
- `error` names its intermediate results.
- `2^MANTISSA_BITS` and `T::one()` are computed by the helpers `pow2_mantissa_bits` and
  `float_one`.
- The unsized function clones the data only when it must shuffle it.
- `can_float_sum_overflow` destructures `bounds` in its body.
- The `inf_log2` impls are generated with a contract.

### `make_bounded_float_ordered_sum`, `make_sized_bounded_float_ordered_sum`

These sum with saturating float addition, `clamp(a + b, MIN, MAX)`. The derivation in the code
compares the result with the ideal sum, which fails once sums saturate. The proof instead
compares it with the exact sum clamped at every step, `csum`:

1. **Rounding error (Lean, `Saturating.lean`):** the sequential saturating float sum of `n`
   values bounded by `m` is within `2^-p n^2 m` of `csum` (`satSeqSum_err`).
   - Clamping is 1-Lipschitz, so each step adds at most its rounding error, `2^-p |s + x|`.
   - The partial sums stay below `k M` after `k` steps, as in the overflow proof, with
     `M <= 2 m` a power of two.
   - The code's error bound, `n^2 2^-MANTISSA_BITS m`, is twice this.
2. **Stability of `csum` (Creusot, `verification/clamped.rs`):** under the insert-delete distance,
   `|csum(x) - csum(y)| <= d_in max(|L|, U)`, and `(d_in / 2) (U - L)` for equal sizes. This is
   the real counterpart of the integer ordered sums' proof.
3. **The constructors meet their contracts** (`rust/src/transformations/sum/float/ordered/proof.rs`)
   for any `S`, and for `S = Sequential<T>` the two combine into stability:
   `|f(x) - f(y)| <= e + d_in * sensitivity + e`. The unsized sum truncates longer datasets to
   their first `size_limit` values. The theorem covers datasets of at most `size_limit` values. A
   brute-force search over clamped integer sums found no counterexample with truncation either.

The same searches found that **pairwise** saturating sums are not stable. Removing one element
regroups the rest, and clamping depends on the grouping (`FINDINGS.md` F2). `make_sum` used them
for `f32` and `f64` whenever the checked sum could overflow, which broke stability under
`InsertDeleteDistance`; it now uses sequential summation there (below). Under `SymmetricDistance`,
`make_sum` shuffles first: the proof no longer went through, but an exact search found no
neighbouring pair whose shuffled outputs cannot be coupled within the map
(`scripts/pairwise_ordered_sum_shuffled.py`).

Mutation checks: each of the following makes verification fail:
- `d_in / 3` in the sized map;
- the unsized sensitivity `U - L` instead of `max(U - L, |L|, U)`;
- no relaxation in the map.

Code changes: none (contracts only). The sequential `error_bound` is now `n u a`, weaker than the
cited `(n - 1) u a`, so that it also bounds the saturating sum.

### `make_sum` (dispatch)

Proved (`rust/src/transformations/sum/proof.rs`): for every integer and float type and both input
metrics, if `make_sum(input_domain, input_metric)` returns `Ok(t)`, then `t` is stable on
`input_domain` (`MakeSum::sum_is_stable`). The input domain is the vectors whose elements lie
within the domain's closed bounds (and, for floats, are finite), with the domain's size if it is
known; for unsized float sums, of at most `DEFAULT_SIZE_LIMIT` (`2^20`) values, as for the leaves.

1. **Each branch returns a verified sum.** Lifting lemmas turn each sum's contract and stability
   theorem into the property for `make_sum` (`int_sym_stable`, `int_id_stable`,
   `float_sym_stable`, `float_id_stable`).
2. **Chaining** (`combinators/chain`, `core/mod.rs`): `make_chain_tt` and `>>` on transformations
   are verified. The chained function runs one function, then the other, and the chained map
   composes the maps. `Function::make_chain` and `StabilityMap::make_chain` were trusted; they now
   call `eval` on the wrapped functions, which is verified (same behavior).
3. **`make_unordered`** (`transformations/cast_metric`) copies its input and maps `d` to at least
   `d`. Insert-delete neighbours are symmetric neighbours (`verification/cast_metric.rs`,
   `id_close_sym_close`), so `make_unordered >> (checked sum)` is stable under
   `InsertDeleteDistance`.
4. **`make_ordered_random`** returns a permutation of its input (trusted `Shuffle` contract) and
   maps `d` to at least `d`. Its output is random, so the theorem for
   `make_ordered_random >> (sequential saturating sum)` under `SymmetricDistance` is a matching
   (`float_sym_shuffled_stable`):
   - every output is the saturating sum of some ordering of the input;
   - for neighbours `x`, `y` within `d`, every ordering of `x` is matched with an ordering of `y`
     whose sum is within the map at `d`.

   The matching uses `shuffle_match` (trusted, `TRUST.md`): orderings of symmetric neighbours can be
   matched within insert-delete distance `d`. Stability of the randomized output then needs this
   matching to couple a uniform shuffle of `x` with one of `y`, which is cited from the proof of
   `make_ordered_random`, not mechanized.

Code changes:
- The four saturating float branches use `Sequential` instead of `Pairwise` (the fix for F2,
  with a regression test).
- The dispatcher's branches move from the two macros into four generic functions (integers and
  floats, times the two metrics). The macro impls delegate to them, so each is verified once
  rather than per type.
- The chained branches bind the two transformations before `>>`, with the same evaluation order.

Mutation checks: each of the following makes verification fail:
- one saturating float branch reverted to `Pairwise`;
- `make_unordered`'s map returning `d_in / 2`;
- `make_ordered_random`'s map scaled by 0, or its function not shuffling.

### `can_float_sum_overflow` (Lean)

Proved (`verification/lean/OpenDPVerification/Float/`): for `f32`, `f64` and every IEEE binary
format with precision at least 2, if `can_float_sum_overflow(size, (lower, upper))` returns
`Ok(false)`, then summing any dataset of at most `size` values within `[lower, upper]` does not
overflow: `Sequential` and `Pairwise` respectively (`canOverflowSeq_sound`,
`canOverflowPw_sound`). The transformations rely on this, as they sum without checking for
infinities.

- `Format.lean`: formats with unbounded exponent range, round-to-nearest-even (`rne`), and its
  properties: it returns a nearest value of the format, is monotone and odd, and fixes values of
  the format.
- `Sum.lean`: the two summation algorithms and the overflow arguments. By monotonicity, a dataset
  bounded by `M = 2^c` sums to at most the sum of all `M`s. Sequentially, that is
  `min(k, 2^p) * M`, as each further addition of `M` is a tie that rounds down to even.
  Pairwise, it is at most `RU(k) * M`, where `RU` rounds up to the format, because
  `RU(a) + RU(b) <= RU(a + b)` for halves `|a - b| <= 1`. Check 1 is handled separately:
  sequentially, an addition of less than half an ulp of `MAX` rounds back to `MAX`; pairwise,
  `n * mag < ulp(MAX)` leaves a large margin.
- `Overflow.lean`: a line-by-line model of the Rust code over abstract primitives that are only
  assumed to meet their contracts (`TRUST.md`), and the soundness theorems.

Before the proofs, an exhaustive search over tiny formats (`scripts/float_sum_overflow_search.py`)
found no counterexample. It also showed that the sequential check is unsound under any tie rule
other than ties-to-even (`FINDINGS.md` D2).

Mutation checks: each of the following makes the proof fail. Each also makes the claim false, for
some primitives that meet the weakened contracts:
- check 1 compares against `ulp(MAX)` instead of `ulp(MAX) / 2`;
- the pairwise limit is rounded up (`inf_div`) instead of down;
- `inf_mul` may return `Ok(inf)`;
- the size is rounded down when cast.

No code changes.

## Status: `make_count_by`

Verified (`rust/src/transformations/count/proof.rs`), for every key type `TK` and integer count
type `TV`:

1. **The constructor meets its contract.** The function can be evaluated on any dataset. It
   returns a map from each value occurring in the data to its number of occurrences, saturated at
   `TV::MAX`, and has no other keys. The stability map returns at least `(d_in, d_in, d_in)`.
2. **Stability.** On datasets within symmetric distance `d_in`, the count maps are close under
   `L01InfDistance` (absent keys count as 0):
   - each count differs by at most `d_in` (L∞);
   - for any finite set of distinct keys, the differences sum to at most `d_in` (L1), and at most
     `d_in` of the counts differ (L0).

   Bounding the sums for every finite key set is equivalent to bounding the norms, because only
   finitely many counts are non-zero.

The proof writes `x = c + a`, `y = c + b` as multisets with `|a| + |b| <= d_in`. Saturation is
1-Lipschitz, so each count moves by at most `count(a, k) + count(b, k)`. Summed over distinct keys,
that is at most `|a| + |b|`. The L0 distance is at most the L1 distance because counts are
integers. Datasets are modeled by the deep models of their elements, with a generic multiset model
(`verification/multiset.rs`).

Trusted: `count_by_map` (the counting loop, `TRUST.md`), as `HashMap::entry` has no specification
in Creusot.

Mutation checks: each of the following makes verification fail:
- halving the L0 or the L1 component of the stability map;
- halving the L1 component and weakening the contract to match (the theorem fails);
- stating the L1 bound for key sequences that may repeat keys.

Code changes (behavior unchanged):
- The counting closure is moved into `count_by_map`.
- `TK` gains a `MaybeDeepModel` bound, which is empty outside Creusot.
- The other constructors in the module (`make_count`, `make_count_distinct`,
  `make_count_by_categories`) are marked trusted, as they are out of scope.

## Status: `make_clamp`

Verified (`rust/src/transformations/clamp/proof.rs`), for every atom type `TA` and event-level
metric `M` (`SymmetricDistance`, `InsertDeleteDistance`, `ChangeOneDistance`, `HammingDistance`):

1. **The constructor meets its contract.** On success:
   - The input domain excludes null values (`assert_non_nan`).
   - The bounds are ordered, `lower <= upper`, in the order of `ProductOrd`.
   - The output domain has the closed bounds `bounds`, excludes null values, and keeps the input's
     size.
   - The function can be evaluated on any dataset. Its outputs clamp each row
     (`y = x.map(clamper(bounds))`), and every output row lies within the bounds.
   - The function succeeds on every dataset of non-null rows.
   - The stability map returns at least `d_in`.
2. **Stability.** On datasets within distance `d_in` under `M`, the outputs are within the
   stability map at `d_in`. Applying any function to each row preserves each of the four
   distances (`verification/rows.rs`), so this holds for any row function.
3. **Composition with `make_sum`.** Clamped integers lie within the bounds as integers, and floats
   clamped to finite bounds are finite and lie within the bounds as reals. These are the input
   assumptions of the `make_sum` proofs (`clamp_int_bounded`, `clamp_float_bounded`).

`make_row_by_row_fallible` is verified on its own contract (`row_by_row_contract`). Its function
maps each row by the row function, and fails only if the row function fails on some row.
`ProductOrd` gets a ghost model:
- an order `ple`, `non_null`, and whether the order is `total`;
- `clamped`, the result of `total_clamp`: compare with the bounds for totally ordered types, and
  clamp each component for pairs.

`total_cmp` (integer, `IBig`, `RBig` and pair impls), `total_gt` and every `total_clamp` are
verified against it. The float `total_cmp` is trusted.

Found and fixed: F3 (`FINDINGS.md`). Pairs are ordered componentwise, so clamping them used to
fail depending on the data. This was reachable from Rust only.

Trusted: `ord_clone`, `int_ple`, `float_ple`, the float `ProductOrd` contract and the
`Ordering::is_*` specifications (`TRUST.md`).

Mutation checks: each of the following makes verification fail:
- removing the construction-time check of the bounds;
- swapping the bounds in the row function, or clamping only from below;
- a stability map of `0` in `make_row_by_row_fallible`;
- skipping the last row in `apply_rows`;
- declaring pairs totally ordered (the pair `total_cmp` fails);
- ordering pairs by "either component" instead of both;
- returning `max` instead of `min` for values below `min` in `total_clamp`;
- swapping the bounds of one component in the pair `total_clamp`;
- failing the pair `total_clamp` on rows that are not ordered with the bounds.

Code changes:
- `make_clamp` builds the output row domain with `AtomDomain::new_closed`. The value is the same,
  since the input domain was checked to exclude NaN.
- `make_clamp` checks the bounds with `ProductOrd::total_gt`, rejecting pair bounds that are not
  ordered componentwise (F3). This changes behavior for pairs only.
- `total_clamp` has no default body. Totally ordered types expand the previous algorithm
  (`clamp_by_cmp_body!`); pairs clamp componentwise (F3). The FFI and polars impls call
  `clamp_by_cmp` and are unchanged.
- `apply_rows` for vectors is an indexed loop rather than `iter().map(..).collect()`, with the
  same results.
- `traits::operations` is no longer a trusted module. Items in it outside the scope are trusted
  individually.

## Status: `make_laplace` (phase 1: deterministic code)

Verified, for every atom type (floats and integers, scalar and vector inputs): `make_laplace`
returns valid measurements under `P = 1` (`noise_claim`), and for `f64` vectors and scalars and
`i32` vectors, valid measurements (`make_laplace_*_valid`), given the assumptions listed in
`TRUST.md`:
- the discrete Laplace mechanism theorem (cited);
- chaining and post-processing (cited);
- the definitions of the metrics;
- **the samplers draw the distributions they claim (not verified: phase 3)**.

What is proved:

1. **The float discretization** (`make_float_to_bigint`, `nature/float/proof.rs`). Each value is
   clamped to the finite range and rounded to the nearest multiple of `2^k`, ties up
   (`find_nearest_multiple_of_2k`, `floor_div`, `x_mul_2k`). On datasets in the input domain
   within L1 distance `d_in`, the integer outputs are within `(d_in + rounding_distance) / 2^k`,
   where `rounding_distance = size (2^k - 2^min_k)` (`get_rounding_distance`). Finite floats are
   multiples of `2^min_k`, so rounding two of them moves their difference by less than `2^k`,
   hence by at most `2^k - 2^min_k` (`round_lipschitz`, in integers).
2. **The integer conversion** (`make_int_to_bigint`) and **`make_vec`** preserve distances.
3. **The Laplace privacy map** (`NoisePrivacyMap` for `ZExpFamily<1>`): it rejects negative
   scales and distances, returns 0 at `d_in = 0`, infinity when `scale = 0`, and otherwise
   `d_in / scale` rounded up. This is the hypothesis of the mechanism theorem.
4. **The mechanisms** (`MakeNoise` for integer vectors, the float and integer natures, `IBig`
   scalars, `DiscreteLaplace`) and **`make_laplace`**: each chains these pieces with `>>`, whose
   specifications are now verified. On the float path the noise scale is `scale / 2^k` on the
   integer grid, so the loss is `((d_in + rounding_distance) / 2^k) / (scale / 2^k)`.

`MakeNoise` has a ghost `noise_claim`: `m_valid(m)` for the verified impls (for `P = 1`), and
`true` (no claim) for the Gaussian and geometric impls, which are out of scope.

No bugs found.

Mutation checks: each of the following makes verification fail:
- the rounding distance without the factor `size` (code and contract): the stability theorem
  fails;
- no rounding distance at all (code and contract): the stability theorem fails;
- a stability map scaling by `2^k` instead of `2^-k`;
- a privacy map rounding down (`neg_inf_cast`);
- no check that the scale is non-negative;
- no check that the input domain excludes NaN;
- rounding down instead of to nearest.

Code changes (behavior unchanged):
- The closures of `make_float_to_bigint`, `make_int_to_bigint` and the Laplace privacy map are
  moved into functions with contracts (`discretize_vec`, `discretized_distance`,
  `ints_to_bigints`, `to_rbig`, `laplace_loss`); the iterator chains become indexed loops.
- `dashu` constants are replaced: `RBig::ONE` and `RBig::ZERO` by `RBig::from(1usize)` and
  `RBig::from(0usize)`, and comparisons with zero by `sign()`. The literal `0.0` of the privacy
  map is returned by `zero_loss()`.
- In `get_rounding_distance`, the factor is computed before `distance *=`.
- `MakeNoise` for integer vectors computes the privacy map before moving `self` into the noise
  function (`noise_function`), instead of cloning it.
- `AtomDomain` and `VectorDomain` have hand-written `Clone` impls (the same as the derived ones).

Remaining phases: the mechanism theorem in Lean (phase 2), and the samplers (phase 3).
