# Formal verification of OpenDP (proof of concept)

Machine-checked verification of selected OpenDP components with
[Creusot](https://github.com/creusot-rs/creusot), a deductive verifier for Rust.

- [`TRUST.md`](TRUST.md): everything the proofs assume rather than prove.
- [`FINDINGS.md`](FINDINGS.md): bugs and other issues found along the way.

## Running

Requirements:

- Creusot v0.14.0 (`cargo creusot`), installed per its README.
- OpenDP's fork of `creusot-std`, which adds models for `dashu` numbers
  (branch `opendp-dashu` of a Creusot checkout).

```sh
export CREUSOT_STD_PATH=/path/to/creusot/creusot-std
tools/creusot.sh                                      # compile and prove everything in scope
tools/creusot.sh 'transformations::sum::int::checked::*'   # prove one module
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
| `make_(sized_)bounded_int_ordered_sum` | Not started |
| `make_(sized_)bounded_int_split_sum` | Verified: contracts and stability theorems (sized and unsized). |
| `make_(sized_)bounded_float_checked_sum` | Not started |
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
