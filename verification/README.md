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
tools/creusot.sh 'transformations::sum::*' 'verification::*' 'traits::*'   # the verified components
tools/creusot.sh 'transformations::sum::int::checked::*'                   # one module
```

The float ordered sums (not started yet) fail. A run without a filter also covers code outside
the verified components that is not yet marked trusted, and reports failures there: `Debug` impls,
`invoke`, and `PartialEq` for metrics.

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
| `make_(sized_)bounded_float_ordered_sum` | Not started |
| `make_sum` (dispatch) | Not started |

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
