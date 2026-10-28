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
  'transformations::resize::*' 'transformations::impute::*' 'combinators::chain::*' \
  'measurements::noise_threshold::*' 'measurements::noise::*' \
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

The samplers (`verification/samplers`, the same Lean and Mathlib, plus Aeneas's Lean library):
Charon and Aeneas must be built next to this repository (`../charon` at the commit in
`../aeneas/charon-pin`, and `../aeneas`; see "Phase 3" below).

```sh
cd verification/samplers
./extract.sh --check   # the committed extraction matches the Rust code
cd lean
lake exe cache get
lake build             # check the extracted code and the proofs about it
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

## Status: `make_resize`

Verified (`rust/src/transformations/resize/proof.rs`) for every atom type `TA` and each of the
four metric pairs, after fixing F4 (`FINDINGS.md`).

1. **The constructor meets its contract** (`resize_contract`). On success:
   - `size > 0`.
   - The output domain is the input's element domain with `size` rows.
   - The function can be evaluated on any dataset. Its output on `x` is described by `resize_out`:
     - if `x` has at most `size` rows, `x` padded with `constant`, shuffled when the output metric
       is ordered and the input metric is not;
     - otherwise the first `size` rows of `x`, shuffled first when the input metric is unordered.
   - The stability map returns at least `2 d_in`.
2. **The possible outputs.** A shuffle is uniform (`Shuffle`'s Proof Definition), so the support of
   the output on `x` is `resized`: as above, with any ordering in place of a shuffle
   (`out_resized`).
3. **Stability, as a matching.** For datasets `x`, `y` within `d` under the input metric, every
   possible output of `x` is matched with a possible output of `y` within `2 d` under the output
   metric (for every ordered pair, so in both directions):
   - `SymmetricDistance` to `SymmetricDistance`: `resize_sym_sym_stable`;
   - `SymmetricDistance` to `InsertDeleteDistance`: `resize_sym_id_stable`;
   - `InsertDeleteDistance` to `SymmetricDistance`: `resize_id_sym_stable`;
   - `InsertDeleteDistance` to `InsertDeleteDistance`: `resize_id_id_stable`. The function is
     deterministic, so this is stability.

   Where one side is deterministic, the matching is the coupling. Where both are shuffled, that the
   matching extends to a coupling of the uniform shuffles is assumed (`TRUST.md`).

The matchings are built from decompositions of the datasets into a common part and extra rows:
- padding moves the shared constants into the common part (`match_pad_pad`);
- truncating splits an ordering into its first `size` rows and the rest (`split`,
  `match_trunc_trunc`, `match_trunc_pad`, `match_pad_trunc`);
- under the insert-delete distance, prefixes of `x` and `y` keep a prefix of their common
  subsequence (`sub_prefix`, `sub_drop`), so the first `size` rows of datasets within `d` are within
  `2 d` (`id_prefix`, `match_id_pad_trunc`, `id_pad_trunc`), and padding at the end extends the
  common subsequence (`id_pad_pad`);
- for an ordered output, `reorder` orders the rows of `y`'s output like the matching rows of
  `x`'s output, so that they differ in at most `|a|` positions, and hence are within insert-delete
  distance `2 |a|` (`hamming_id`).

Found and fixed: F4 (`FINDINGS.md`). From `InsertDeleteDistance` to `InsertDeleteDistance`, a
dataset of exactly `size` rows was shuffled while its neighbour with one more row was truncated
without a shuffle, so the transformation was not stable. Before the fix this was proved
(`resize_id_id_unstable`, commit `2e2cc8a4`): with distinct `a`, `b`, `c` and `size = 3`, `[a, b, c]`
and `[a, b, c, a]` are within distance 1, the first could be resized to `[c, b, a]`, and the only
output of the second, `[a, b, c]`, is at distance 4 > `map(1)` = 2. The padded dataset is now
shuffled only when the input metric is unordered and the output metric ordered.

Also strengthened: `Shuffle::reorders` is now uninterpreted, implying a permutation but not
equivalent to one. Before, the identity counted as a shuffle, so removing `data.shuffle()` from
`make_ordered_random` still verified; now it fails.

Trusted: `atom_clone`, `perm_same`, the coupling of matchings where both sides shuffle, and the
`Shuffle` specification (`TRUST.md`).

Mutation checks: each of the following makes verification fail:
- removing the shuffle of padded datasets, or of datasets before truncating;
- reverting the fix of F4 (shuffling padded datasets whenever the output metric is ordered);
- truncating to `size - 1` rows;
- a stability map of `d_in` instead of `2 d_in`;
- removing the shuffle from `make_ordered_random`.

Code changes:
- F4: the padded dataset is shuffled only when the output metric is ordered and the input metric
  is not. This changes behavior only from `InsertDeleteDistance` to `InsertDeleteDistance`, where
  the order of the rows is now kept.
- The function's closure calls `resize_vec`, and the padding is built by `pad`, an indexed loop,
  instead of an iterator chain.
- `IsMetricOrdered` requires `MaybeEventModel` (empty outside Creusot).
- `transformations::resize` is no longer a trusted module.

## Status: `make_impute_uniform_float`

Verified (`rust/src/transformations/impute/proof.rs`) for `f32` and `f64` and every event-level
metric `M`, after fixing F5 (`FINDINGS.md`).

1. **The constructor meets its contract** (`impute_uniform_contract`). On success:
   - The bounds are finite, with `lower < upper`.
   - The output domain excludes NaN, and keeps the input's size.
   - The function can be evaluated on any dataset and never fails. Each output row is the input row
     if it is not NaN, and otherwise a finite value in `[lower, upper)` (`imputed`). No output row
     is NaN.
   - The stability map returns at least `d_in`.
2. **Stability** (`impute_uniform_stable`). For datasets `x`, `y` within `d` under `M`, every
   possible output of `x` is matched with a possible output of `y` within the map. The row function
   is random, so it relates rows to outputs instead of mapping them. `EventModel::close_rel`
   (`verification/rows_rel.rs`) shows, for each of the four event-level metrics, that relating
   every row by the same relation preserves closeness. Rows shared by `x` and `y` keep their
   outputs, and the other rows of `y` take any related output. The proof pairs each row with its
   output, lifts the witness of closeness (multiset decomposition, common subsequence, or
   positions) to the pairs, and projects onto the outputs with `close_map`. That this matching is a
   coupling (the shared rows get the same sample) is assumed (`TRUST.md`).
3. **`make_row_by_row`** now has a contract (`row_by_row_infallible_contract`), proved from
   `make_row_by_row_fallible`'s.

Found and fixed: F5, infinite bounds were accepted, and the first NaN row then panicked. Found and
recorded: F6, bounds whose width overflows are sampled only in part, and D6, the random row function
is outside the cited proof of `make_row_by_row`.

Trusted: `sample_uniform` (`rand`'s preconditions and range), `is_nan`, `lt`, `is_finite`,
`finite_non_null`, `AtomDomain::new_non_nan`, and the coupling of row-by-row relations
(`TRUST.md`).

Mutation checks: each of the following makes verification fail:
- removing the finiteness check (F5), or the check that `lower < upper`;
- imputing every row, or no row;
- an output domain that allows NaN.

Code changes:
- F5: `make_impute_uniform_float` rejects non-finite bounds.
- The row closure calls `impute_row`. The sampling, the NaN test and the comparison of the bounds
  are wrapped in `sample_uniform`, `is_nan` and `lt`, with the same results (`lower >= upper` is
  `!(lower < upper)` once NaN is excluded).
- `transformations::impute` is no longer a trusted module. Its other items are trusted
  individually.
- `same_len`, `count_push`, `sub_same` and `id_witness` moved from `make_resize`'s proof to
  `verification/{multiset,rows}.rs`.

## Status: `make_laplace_threshold`

Verified (Creusot, with the mechanism theorem cited, as `make_laplace` phase 1) for every atom
type (floats and integers), after fixing F7 and F8 (`FINDINGS.md`): `make_laplace_threshold`
returns valid measurements (`noise_threshold_claim`; for `f64` and `i32` counts keyed by `String`,
`make_laplace_threshold_{f64,i32}_valid`), given the assumptions in `TRUST.md`, including:
- the threshold mechanism theorem (cited, Rogers 2023);
- the samplers draw the distributions they claim (not verified);
- the definition of `L0PInfDistance` on maps.

What is proved:

1. **The privacy map** (`threshold_loss`, `rust/src/measurements/noise_threshold/distribution/laplace/`):
   it floors the sensitivities, tightens `l1` and `li` against each other, returns `(0, 0)` for zero
   sensitivity and `(∞, 1)` for zero scale, and otherwise `ε` from the Laplace map and
   `δ = 1 - (1 - δ1)^l0` (rounded up, capped at 1), where `δ1` is the smaller computable tail bound
   at `T - Δ∞`. This is `threshold_bound`, the hypothesis of the cited theorem.
2. **The release rule**: a pair is kept when its noisy value is strictly beyond the threshold
   (`is_beyond`).
3. **The conversions** of float and integer maps to integer maps (`nature/`): keys are kept, and
   values are converted exactly or rounded to multiples of `2^k`. Per key, rounded values differ by
   at most `(|a - b| + 2^k - 2^min_k) / 2^k`, also against a missing key (`map_rounding_stable`,
   from `make_laplace`'s `elem_bound` and the new `absent_bound`). The stability maps add this slack
   `l0` times to the L1 distance and once to the L∞ distance.
4. **The mechanisms and `make_laplace_threshold`**, chaining these with `>>`.

Found and fixed:
- F7: the map computed `δ` from `Pr[Z > T - Δ∞]`, while keys with `v + Z = T` were released. Fixed
  by releasing only values strictly beyond the threshold. Proved before the fix
  (`Threshold.lean`: `threshold_delta_too_small`), and after it the tail the map computes is the
  release probability (`releaseProbStrict_eq`, `discrete_bound_eq`).
- F8: keys with value 0, which the metric equates with missing keys, were released with positive
  probability (`zero_key_released`). Fixed by dropping them before adding noise.

Both fixes change the shared release rule, so `make_gaussian_threshold` changes too (and its F7
analogue is fixed); it is not verified.

Mutation checks: each of the following makes verification fail:
- releasing values equal to the threshold (reverting F7);
- the tail bound one step too far, or computed for one key instead of `l0`;
- no check that the threshold is at least the L∞ sensitivity;
- the float conversion's L1 slack added once instead of `l0` times, or no slack on L∞;
- swapping the L1 and L∞ distances in the integer conversion.
Removing the zero filter (F8) is not caught: it is in the trusted noise function, and is covered by
`test_laplace_threshold_drops_zero_keys`.

Code changes:
- F7: the release rule is `v + Z > T` (`< T` for a negative threshold), and the docs say so.
- F8: zero values are dropped before noise is added.
- The privacy map closure calls `threshold_loss`; the float arithmetic for `δ` is in `joint_delta`
  and `min_one`. The noise function is `noise_threshold_function`, with the keep rule in
  `is_beyond`.
- The conversions use `map_values` with per-value helpers (`discretize_value`,
  `IBig::from`) and distance helpers (`float_threshold_distance`, `int_threshold_distance`), and
  clone only the key domain instead of the whole input domain.
- `measurements::noise_threshold` is no longer a trusted module; out-of-scope items are trusted
  individually. The Laplace noise map (`make_laplace`) states its bound in its contract.

## Status: `make_expr_fill_null` (Polars, Lean and tests)

`make_expr_fill_null` builds the Polars expression `data.fill_null(fill)` and claims an output
domain (the data's, without bounds or nulls) and the stability map `d_in ↦ d_in`. OpenDP computes
nothing itself, so there is no floating-point arithmetic to model. What matters is whether the
claims hold for what Polars computes.

- **Lean** (`verification/lean/OpenDPVerification/FillNull.lean`), on a per-row model of
  `fill_null`:
  - `fill_member`: the output is in the claimed domain when every fill value satisfies the data's
    predicate;
  - `fill_stable`, `fill_stable_scalar`: `d_out ≤ d_in` under the symmetric distance, for column
    and scalar fills;
  - `fill_member_fixed`, `fill_noNaN_fixed`: with the fix of F20, the output is always in the
    claimed domain, and a domain without NaN means no output value is NaN;
  - `fill_nan_counterexample` (F20) and `null_leak` (F21), about the code before the fixes.
- **Conformance tests** (`expr_fill_null/test.rs`, `test_fill_null_model_*`): Polars' output is
  the model's, bit for bit, on random columns (NaN, infinities, signed zeros, nulls), for column and
  scalar fills, in row-by-row and aggregation contexts. Every output is a member of the output
  domain.
- **Creusot is not possible here:** its toolchain cannot compile Polars.

Found and fixed:

| | Bug | Shown by | Fix |
| --- | --- | --- | --- |
| F19 | the output's type is the supertype of the data's and the fill's; the domain keeps the data's | running it (`test_fill_null_keeps_dtype`) | the fill must have the data's type; numeric literals the data's type holds exactly are converted to it |
| F20 | a fill that can be NaN puts NaN in a column whose domain excludes it | Lean (`fill_nan_counterexample`) and running it (`test_fill_null_nan`) | the output's NaN flag is the data's or the fill's (`fill_member_fixed`) |
| F21 | through F20, one null row moves a released sum from `n` to about 0: a privacy violation | Lean (`null_leak`) and the released package (`verification/scripts/fill_null_counterexamples.py`) | the fix of F20: `sum` rejects the query |

The tests of F19 and F20 fail on the code before the fixes. `dp.quantile` filled nulls with an
`f64` median; it now converts the median to the data's type.

```sh
cd rust && cargo test --features untrusted,polars --lib expr_fill_null  # passes
uv run --with opendp==0.16.0 --with polars==1.36.1 --with pyarrow \
  python -I verification/scripts/fill_null_counterexamples.py           # F21 in the release
```

Mutation check: building `fill.fill_null(data)` instead of `data.fill_null(fill)` makes 4 tests
fail.

## Status: `filter` (Polars, Lean and tests)

`make_stable_filter` builds `LazyFrame.filter(predicate)` and `make_expr_filter` builds
`expr.filter(by)` (in an aggregation context). As with `fill_null`, OpenDP only builds the plan, so
what matters is whether the claims hold for what Polars computes. They do; no bugs were found.

- **Lean** (`verification/lean/OpenDPVerification/Filter.lean`), on a per-row model of `filter`
  (keep the rows whose predicate is `true`, in order):
  - the output domain: output rows are input rows, so the column domains hold (`filt_sublist`);
    groups only shrink and no group appears, so `max_length` and `max_groups` hold
    (`filt_group_length_le`, `filt_keys`, `filtMap_length_le`);
  - stability `d ↦ d`: for the symmetric distance (`filt_symDist`), the insert-delete distance
    (`filt_idClose`: filtering a shared subsequence gives one of the filtered datasets) and the
    identifier distance (`filt_symIdClose`), lifted to every bound of the frame distance, per group
    and in the number of groups that differ (`filt_frameClose`, `filt_frame_*`); for
    `expr.filter(by)` on each group (`filtMap_symDist`, `filtMap_idClose`);
  - the dropped invariants: filtering does not preserve keys or lengths
    (`filt_keys_not_invariant`, `filt_lengths_not_invariant`), so `make_stable_filter` must drop
    both, and `make_expr_filter` must drop lengths. It keeps keys because Polars keeps empty
    groups in an aggregation, which the tests check.
- **Conformance tests** (`test_filter_model` in `make_stable_lazyframe/filter/test.rs`,
  `test_expr_filter_model` in `make_stable_expr/expr_filter/test.rs`): Polars' output is the
  model's, bit for bit, on random frames (NaN, infinities, signed zeros, nulls) with predicates that
  are columns, comparisons, Kleene `and`/`or` with nulls, and literals; for both distances, in
  `select` and group-by contexts (every input group present, in order). Every output is in the
  output domain (columns, `max_length`, `max_groups`).
- **Assumed:** the predicate, the margins' groupings and the identifier are row functions. The
  identifier is any expression the user gives, and nothing checks this (TRUST.md).

Mutation checks, each caught by the tests:
- the frame filter negating its predicate;
- the frame filter keeping the margins' invariants;
- `make_expr_filter` claiming the lengths invariant;
- `make_expr_filter` swapping `expr` and `by`.

Aside: `FrameDomain::member` errors on a margin with no grouping columns (Polars rejects a group-by
without keys), so the tests check margins themselves. This affects only the membership check.

```sh
cd rust && cargo test --features untrusted,polars-ffi --lib filter
```

## Status: `make_np_clamp` (Python and numpy, Lean)

`make_np_clamp` is Python code over numpy, so Creusot does not apply. Its `_function` is
transcribed by hand into Lean (`verification/lean/OpenDPVerification/NpClamp.lean`). The
transcription runs over a model of the numpy operations it uses:
- IEEE arithmetic on each element, with infinities and NaN;
- `np.linalg.norm` as numpy computes it;
- a summation order that is fixed but unspecified per row length.

The model and the transcription are trusted (`TRUST.md`). F9-F17 were found, and all are fixed
on this branch. `clamp` models the fixed code, and `clampV0` the code before the fixes.

What is proved about the fixed code (for any binary format, so `float64` and `float32`):

1. **Rows are clamped independently** (`clamp_map`). The loop runs over the whole array until
   every row is within the bound, so a row may be divided more often than it needs. But a row
   within the bound has a factor that rounds to at most 1, so further passes leave it unchanged
   (`body_eq_self`). Each output row is therefore a function of its input row alone.
2. **Stability** (`clamp_stable`). On datasets where the function returns, the outputs are no
   farther apart than the inputs under the symmetric distance. This is the claimed map
   `d_in ↦ d_in`.
3. **No NaN** in the output (`clamp_no_nan`).
4. **The output domain's norm check** holds for every output row, for any origin
   (`clamp_member`).
5. **Termination** (`clamp_terminates`), on every dataset, the empty one included (`clamp_empty`).
   - The hypotheses are that `norm` is a normal float, and for `p = 1` also `norm ≥ d · 2^-1022`.
   - Each pass shrinks a normal element of every row above the bound by at least one
     representable step (`abs_rne_div_lt`, `factor_ge`), and a row of subnormals is within such a
     bound.
   - The minimum norm implies the hypotheses (`TermHyp.of_min`, `min_norm_f64`, `min_norm_f32`).
6. **True norms**, with origin zero (`clamp_true_norm`). The loop bounds the norms numpy computes.
   The true norms exceed `norm` by at most a relative rounding error:
   - for `p = 1`, `(1 - 2^-p)^-(n-1)` (`l1_true_norm`);
   - for `p = 2`, about `(n/2 + 2) 2^-p` (`l2_true_norm`, `slack_le`). Squares that underflow are
     negligible above the minimum norm.

Found and fixed (counterexamples F9-F14 proved in Lean against the code before the fixes):

| | Bug | Fix |
| --- | --- | --- |
| F9 | `arg + origin` rounds, so outputs can lie outside the ball (`origin_rounding`) | rows that fail the domain's check after adding `origin` back are replaced by `origin` |
| F10 | squares underflow in the L2 norm, so tiny bounds miss rows (`l2_underflow`) | `norm ≥ 2^-458` (`float64`) / `2^-39` (`float32`) |
| F11 | the loop can run forever for small bounds (`nonterm_subnormal`, `nonterm_normal`) | the same minimum norm |
| F12 | with `norm` the largest float, rows of infinite norm pass (`max_bound_overflow`) | the recheck of F9 |
| F13 | the empty dataset raises, revealing emptiness (`empty_error`) | loop on `.any()`; the domain's check also accepts empty arrays |
| F14 | the output domain keeps `cardinalities` that clamping invalidates (`cardinalities`) | dropped from the output domain |
| F15 | row norms depend on the array's memory layout (by running it) | `np.ascontiguousarray` |
| F16 | `float32` data is clamped to `float32(norm)`, which can exceed `norm` (by running it) | clamp to the largest `float32` at most `norm`; the domain's check compares exactly |
| F17 | the output's type changes: `float32` data with an `origin` array, or integer data (by running it) | float elements only; `origin` converted to the data type |

Each fix has a regression test in `python/test/extras/test_clamp_numpy.py`. Each new test fails on
the code before the fixes, and the existing numpy tests (clamp, mean, sum, PCA, eigenvectors,
domains) pass. They run against the branch's FFI build:

```sh
cd rust && cargo build --features untrusted,ffi --lib && cd ../python
PYTHONPATH=src uv run --no-project --with numpy --with pytest --with scikit-learn \
  --with randomgen --with deprecated python -m pytest test/extras/test_clamp_numpy.py
```

The counterexamples reproduce against the released opendp package (numpy 2.5):

```sh
uv run --with opendp --with numpy python -I verification/scripts/np_clamp_counterexamples.py
```

Mutation checks: each of the following makes the Lean build fail:
- dividing every row by the largest factor in the array (rows are no longer independent):
  `loop_spec` and `clamp_map` fail;
- `max(factor, 1)` replaced by `factor` (rows within the bound are rescaled): `body_eq_self`
  fails;
- looping while a norm is at least the bound, rather than above it (a row exactly at the bound
  would never change): `body_eq_self`, `factor_ge` and the termination proof fail;
- a recheck that does not replace rows outside the ball: `clamp_member` fails;
- a `float64` minimum norm of `2^-459`: `min_norm_f64` fails.

`nonterm_subnormal` and `nonterm_normal` show that the conditions of `clamp_terminates` are
needed: without them the theorem is false.

### Linking the model to the code

The theorems are about the hand transcription, so the transcription and the numpy model are tested
against the code, bit for bit:
- **Executable model** (`verification/lean/OpenDPVerification/NpClampExec.lean`). The same functions
  over `ℚ` instead of `ℝ`, with a computable rounding (square roots included). Each is proved equal
  to the model's, and `ClampQ.clamp_toRes` states that running `clamp` returns the model's result.
  So the program the tests run is the model the theorems are about.
- **numpy's summation order** (`numpyPlan`): numpy's `pairwise_sum` (8 accumulators up to 128
  elements, split in two above), proved to be a `Plan`. All theorems therefore hold for it.
- **Oracle** (`verification/lean/NpClampOracle.lean`): runs the executable model on JSON requests,
  with floats as exact rationals.
- **Tests** (`verification/conformance/test_np_clamp.py`, 18 tests, about 2 minutes):
  - `test_norm`: the model's norm is `np.linalg.norm`. This tests the numpy model: IEEE operations,
    the norm formulas, and the summation tree, for row lengths 0-19 and up to 1500.
  - `test_outside`: the model's `outside` is the output domain's member check, on rows within a
    few ulps of the bound.
  - `test_clamp`, `test_clamp_findings`: the model's `clamp` is `make_np_clamp`'s function, on
    random inputs and on the inputs of the findings. The bound and origin are computed from the
    constructor's arguments as it does.

```sh
cd verification/lean && lake build && cd ../..
PYTHONPATH=python/src uv run --no-project --with numpy --with pytest --with deprecated \
  python -m pytest verification/conformance
```

The tests found F18: with `norm` near the largest float, a row whose norm overflows takes up to
~2^52 passes to clamp. It is open, and the random tests keep `norm` at most half the largest float
for this reason.

Mutation checks:
- the tests fail on each of these changes to `make_np_clamp`:
  - no `np.ascontiguousarray`;
  - no replacement by `origin`;
  - `float32(norm)` as the bound;
- the tests fail when the model's 8 accumulators are combined left to right instead of pairwise
  (the proofs still pass, since the order is not constrained by them);
- the build fails when the executable `nan_to_num` maps infinity to 0 (`nanToNum_toF`).

Code changes (Python):
- `make_np_clamp`:
  - minimum norm, float elements only;
  - `norm_T`;
  - `origin` in the data type;
  - C order;
  - the loop on `.any()`;
  - the recheck with replacement by `origin`;
  - no `cardinalities` in the output domain.
- `array2_domain`'s check computes in the precision of the array, compares with `norm` exactly,
  and accepts empty arrays.

## Status: `make_laplace` (phases 1 and 2: deterministic code, mechanism theorem)

Verified, for every atom type (floats and integers, scalar and vector inputs): `make_laplace`
returns valid measurements under `P = 1` (`noise_claim`), and for `f64` vectors and scalars and
`i32` vectors, valid measurements (`make_laplace_*_valid`), given the assumptions listed in
`TRUST.md`:
- the discrete Laplace mechanism theorem: proved in Lean (phase 2, below); what is trusted is
  that the Lean statement matches the Creusot axiom `laplace_mechanism` (`TRUST.md`);
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

### The discrete Laplace mechanism (Lean, phase 2)

Proved (`verification/lean/OpenDPVerification/Laplace.lean`, `laplace_mechanism`): if integer
vectors `x`, `x'` of the same length are within L1 distance `d`, and the privacy map's output `o`
satisfies `LaplaceBound d s o` (the Creusot `laplace_bound`: `0` at `d = 0`, at least `d / s` when
`s > 0`, or `+inf`), then `x + Z` and `x' + Z`, with `Z` independent discrete Laplace samples of
scale `s`, satisfy `Pr[x + Z ∈ S] <= e^o Pr[x' + Z ∈ S]` for every set `S`. This is the Proof
Definition of `NoisePrivacyMap` for `ZExpFamily<1>` with `MaxDivergence`, which the Creusot proof
assumed as `laplace_mechanism`.

- `discreteLaplace s`: mass `(1 - e^{-1/s}) / (1 + e^{-1/s}) e^{-|z|/s}`, proved to sum to 1
  (two geometric series), or the point mass at 0 when `s = 0`.
- `iid p n`: the product mass `prod_i p(v_i)`, proved to sum to 1; `addNoise p x` is its
  translate by `x`.
- The proof follows OpenDP's `NoisePrivacyMap_for_ZExpFamily1`: the pointwise ratio of masses is
  at most `e^{sum_i |x_i - x'_i| / s}` (reverse triangle inequality per coordinate), and a
  pointwise bound gives the set-wise one by summing. At `d = 0` the inputs are equal.

Mutation check: weakening `LaplaceBound` to `o >= d / (2 s)` makes the proof fail.

Only Lean's standard axioms are used (`#print axioms`: `propext`, `Classical.choice`,
`Quot.sound`).

OpenDP's documentation gave the normalizing constant as `(e^{-1/s} - 1) / (e^{-1/s} + 1)`,
which is negative (`FINDINGS.md` D5); it is corrected on the branch.

Remaining phase: the samplers (phase 3). The Aeneas spike below decides how.

### Phase 3 spike: Aeneas on the discrete Laplace sampler

The question: can Charon and Aeneas turn OpenDP's sampler code (`traits/samplers`: `sample_discrete_laplace`
and what it calls, down to `fill_bytes`) into Lean that a distribution proof can be built on?

Setup: Charon `de8736f` (Aeneas's `charon-pin`) and Aeneas `main`, built next to this repository
(`../charon`, `../aeneas`). Aeneas's Lean library pins Lean v4.35.0 and Mathlib v4.35.0, the same
as `verification/lean`. Two local build problems, both fixed in the tools' setup rather than here:
OCaml 5.3 configured against the Xcode 27 SDK enables `pipe2`/`dup3`, which macOS 26 lacks, so
every OCaml program that opens a pipe crashes (configure with `ac_cv_func_pipe2=no
ac_cv_func_dup3=no`); and zarith must link the arm64 GMP, not Homebrew's x86_64 one.

Results:

1. **On OpenDP's code as is, extraction runs but the model is useless for probability.** Charon
   translates the whole call graph without errors. Aeneas translates everything except
   `sample_geometric_exp_fast` (below). But `fill_bytes` calls `thread_rng()`, a global
   source, so in Lean it is an opaque *deterministic* function, and `sample_standard_bernoulli`
   becomes a constant: two "independent" coin flips are provably equal, and every rejection loop
   either returns at once or never. Aeneas's monad is fixed (`Result`: success, failure,
   divergence) and it no longer threads hidden state through opaque calls, so there is no way to
   give `fill_bytes` a random meaning from the Lean side.
2. **With the randomness source as a parameter, extraction is complete and type-checks.**
   `aeneas-spike/rust/src/lib.rs` is OpenDP's code with `rng: &mut R` (`R: RandomSource`, whose
   `fill_bytes` is OpenDP's) passed down, and one loop restructured. Aeneas then threads the
   source's state through every call (`R → Result (... × R)`), and the output (about 600 lines,
   plus axioms for the 35 `dashu` operations it uses) builds against Aeneas's library.
   `aeneas-spike/extract.sh` reproduces it.
3. **Aeneas rejects a loop with both a `break` and an early return when the code after it branches**
   (here, the `?` in `while !sample_bernoulli_exp(..)? {..}` followed by more `?`s). Moving the code
   after the loop into the accepting branch, so the loop only returns, is the same computation
   and is accepted.
4. **Proofs on the output work.** With a random tape as the state (`aeneas-spike/lean/Samplers/Tape.lean`),
   `sample_standard_bernoulli_tape` (the extracted function returns the low bit of the next
   byte and consumes one byte) is proved by `simp` alone. Loops are Aeneas's `loop`, a
   `partial_fixpoint`, with an unfolding equation and fixpoint induction.

What a full proof would still need on this route:
- the change to OpenDP: an explicit randomness source in the samplers (e.g. generic inner functions,
  with the public ones passing the system source), and the loop restructuring;
- Lean models for the `dashu` operations, as definitions over `ℕ`/`ℤ`/`ℚ` (the same assumptions as
  the Creusot `dashu` specifications), and lemmas relating big-endian bytes to numbers for the
  uniform sampler;
- **a probability layer that does not exist yet**: the uniform measure on tapes, a theorem that
  programs consuming disjoint parts of the tape compose like independent draws, and, for each
  rejection loop, that it terminates with probability 1 and has the expected output distribution
  (from the `partial_fixpoint` unfolding, as a countable union over iteration counts);
- the CKS20 distribution arguments, carried out on the extracted code.

The alternative: [SampCert](https://github.com/leanprover/SampCert) (Lean v4.34.1, Mathlib
v4.34.1) has `DiscreteLaplaceSampleOptimized`, which follows the same CKS20 algorithm
(uniform remainder accepted by a Bernoulli(exp) draw, geometric quotient, division, sign with
`-0` rejected), in its probability monad `SLang` (`probUntil`, `probWhile`), with proofs that it
has the discrete Laplace mass. Transcribing OpenDP's samplers (about 100 lines of Rust) into
`SLang` would reuse that monad and most of those proofs. What it gives up is a mechanical link:
the transcription is checked by review.

**Recommendation at the time: transcribe into SampCert's `SLang` and reuse its proofs; keep the
Aeneas extraction as a cross-check of the transcription's control flow.** (Superseded: to keep the
Lean from drifting away from the code, the proofs are now about the extracted code itself, with
SampCert-style distributions; see the next section.) The Aeneas route's mechanical link is
real, but it needs a source change to OpenDP and a probability layer for tapes and loops that
would be built from scratch, and the code it links is short enough to review line by line. The
first step on the SampCert route is porting SampCert to Lean v4.35 (one minor version).

### Phase 3: samplers, proved on the extracted code (proof of concept)

The samplers are proved about the code Charon and Aeneas extract from `rust/src` itself, so that a
change to the Rust code that breaks the correspondence fails the check:
`verification/samplers/extract.sh --check` re-extracts and compares with the committed Lean
(`lean/Opendp/{Types,Funs}.lean`), and the proofs are about those files.

Proved so far: **`sample_uniform_ubig_below` samples uniformly from `[0, upper)`**, for `upper > 0`
whose bit length fits in a `usize` (`OpenDP.Samplers.Uniform.sample_uniform_ubig_below_with_uniform`,
on the extracted `sample_uniform_ubig_below_with`). Only Lean's standard axioms are used.

How:

- **The code change.** `sample_uniform_ubig_below` calls `sample_uniform_ubig_below_with(&mut
  SystemSource, upper)`, which draws its bytes from `rng: &mut R` (`R: RandomSource`, a new trait
  whose `fill_bytes` has the Proof Definition of `fill_bytes`; `SystemSource` calls `fill_bytes`).
  Behavior is unchanged. Aeneas then threads the source's state through the extracted code.
- **External models** (`lean/Opendp/{Types,Funs}External.lean`, trusted): `UBig` is `ℕ`, and the
  eight operations used (`bit_len`, `div_ceil`, `from_be_bytes`, `-`, `%`, comparisons) are their
  documented behavior, failing where they panic. `extract.sh --check` also fails if the extracted
  code calls an external item without a model.
- **The tape semantics** (`SamplerProofs/Tape.lean`). With `tapeSource`, the source's state is a
  random tape and a sampler is a function of it. `HasDist f μ`: on a tape of independent uniform
  bytes, `f` returns `a` with probability `μ a` (a sub-probability mass function, SampCert's
  `SLang`). It is defined by prefixes: the probability of returning `a` is the sum of `256^-|w|`
  over the words `w` that make `f` return `a`, for programs whose successful runs are all explained
  by such words. The rules follow the shape of the extracted code:
  - `hasDist_pure`, `hasDist_draw`, `hasDist_div`;
  - `hasDist_bind`: a continuation reads fresh bytes, so sequencing composes like independent
    draws;
  - `hasDist_loop`: Aeneas's `loop` (a `partial_fixpoint`) has the supremum of the distributions of
    its truncations to `n` iterations (SampCert's `probWhileCut`/`probWhile`). That every
    successful run of the loop is a run of some truncation is proved by fixpoint induction, for
    bodies that do not fail.
- **The uniform sampler** (`SamplerProofs/Uniform.lean`). One iteration draws `L` bytes and either
  returns their value modulo `upper` (below the threshold) or retries; words of length `L` are the
  numbers below `256^L` (`SamplerProofs/Bytes.lean`), so the truncations are geometric partial sums,
  whose limit is `1 / upper`.

Mutation checks: making the acceptance test `sample <= threshold`, or the threshold `max` (no
correction for the remainder), each makes `extract.sh --check` fail and the proof fail.

Next steps: the other samplers on the discrete Laplace path (`sample_bernoulli_rational`,
`sample_bernoulli_exp1`, `sample_bernoulli_exp`, `sample_geometric_exp_slow`,
`sample_geometric_exp_fast`, `sample_standard_bernoulli`, `sample_discrete_laplace`), each with the
same `_with` change (and the loop restructuring in `sample_geometric_exp_fast`); their
distributions, reusing SampCert's lemmas about `probWhile` once SampCert is ported to Lean v4.35;
and the `Sample` impl for `ZExpFamily<1>`, to replace the trusted `noise_function`.
