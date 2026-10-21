# Trust table

Everything the proofs assume rather than prove. A trusted item *without* a contract is merely
skipped: nothing about it is assumed, so verified code cannot rely on its behavior. A trusted item
*with* a contract is an assumption: the contract is believed, not checked.

## Assumptions (trusted contracts)

| Item | Location | Assumed | Justification |
| --- | --- | --- | --- |
| `Function::{new, new_fallible, eval, clone}` | `core/mod.rs` | The ghost model (`pre`, `post`) records / replays the contract of the wrapped closure. | The bodies only wrap and call the closure; Creusot cannot see through `dyn Fn`. |
| `StabilityMap::{new, new_fallible, eval, clone}` | `core/mod.rs` | As above (`post`); the closure must be total. | As above. |
| Float `Inf{Add,Sub,Mul,Div}`, `AlertingAbs`, `Alerting*`, `Saturating*` (`saturating_add_logic` opaque), `Inf{Ln,Log2,Exp,...}`, `InfPowI` | `traits/arithmetic/mod.rs` | The trait contracts (e.g. `inf_add`: `out >= self + v`; `inf_log2`: `out >= log2(self)`). | Implemented with `dashu` arbitrary-precision floats; not verifiable in Creusot. Candidate for testing / Kani. |
| Accuracy of float `Inf{Add,Sub,Mul,Div}` and `inf_log2` (`RealModel::rounds_close`) | `traits/arithmetic/mod.rs`, `verification/mod.rs` | The result is within `|v| / 2 + 2^-10` of the exact value `v`. Not part of the Proof Definitions (`FINDINGS.md` D4). | Correct directed rounding moves a value by at most one unit in the last place. `true` (no assumption) for other types. |
| Integer `inf_div` | `traits/arithmetic/mod.rs` | `out >= self / other` (as reals). | `num::Integer::div_ceil` has no specification. Panics on `MIN / -1` (`FINDINGS.md` F1). |
| `pow2_mantissa_bits` | `transformations/sum/float/mod.rs` | `_2.inf_powi(MANTISSA_BITS)` is exactly `2^MANTISSA_BITS`. | Powers of two are computed exactly (`FINDINGS.md` D4). |
| `float_one` | `transformations/sum/float/mod.rs` | `T::one()` is 1. | `num::One` has no specification. |
| `FloatModel` for `f32`, `f64`; `float_facts` | `verification/float.rs` | `finite` is opaque; `mantissa_bits` is 52 / 23 (as `MANTISSA_BITS`); for every `Float`, `mantissa_bits >= 23` and `rounds_close` is the bound above. | `f32` and `f64` are the only implementors of `Float`. |
| `log2_ge`, `log2_le` | `verification/float.rs` | `log2` is increasing and `log2(2^j) = j`. | Mathematics. |
| `UncheckedSum::unchecked_sum` (`Sequential`, `Pairwise`) | `transformations/sum/float/checked/mod.rs` | If the sum does not overflow (`sum_finite`), its rounding error is at most `error_bound(n, sum of |x_i|, e)`: `(n - 1) u sum |x_i|` (sequential), `gamma(ceil(log2 n)) sum |x_i|` (pairwise), with `u` the unit roundoff. | Cited: Rump (2012), Jeannerod & Rump (2013) for recursive summation, valid for any `n`; Higham (2002), §4.2 for pairwise summation. Float addition is IEEE 754 round-to-nearest (Rust's semantics). |
| `SaturatingSum::saturating_sum` (`Sequential`, `Pairwise`) | `transformations/sum/float/ordered/mod.rs` | Returns `saturating_sum_logic(arg)`: opaque. | Defines the model; the facts about it are below. |
| `seq_saturating_sum_error` | `transformations/sum/float/ordered/proof.rs` | The sequential saturating sum of finite values bounded by `m` is within `n^2 m u` of the clamped exact sum `csum(x, MAX)`. | Proved in Lean (below). |
| `FloatModel::max_finite` for `f32`, `f64` | `verification/float.rs` | Opaque, positive (`float_facts`). | `MAX`; the same constant as the Lean `maxFinite` (by name). |
| `CanFloatSumOverflow::can_float_sum_overflow` (`Sequential`, `Pairwise`) | `transformations/sum/float/checked/mod.rs` | `Ok(false)` implies that summing at most `size` finite values within `bounds` does not overflow (`sum_finite`, opaque). | Proved in Lean (below). `sum_finite` corresponds to `seqSum` / `pwSum` not overflowing; the correspondence is by name. |
| Signed integer `alerting_abs` | `traits/arithmetic/mod.rs` | `out = |self|`. | Wraps `checked_abs`, which `creusot-std` does not specify. |
| `InfCast`, `ExactIntCast` (all impls) | `traits/cast/mod.rs` (trusted module) | `inf_cast`: `out >= v`; `neg_inf_cast`: `out <= v`; `exact_int_cast`: `out = v`. | Module includes float casts Creusot cannot translate. Integer-to-integer impls could be verified. |
| `ProductOrd::total_max` | `traits/operations/mod.rs` (trusted module) | Returns one of its arguments, at least as large as both. | Generic comparisons; floats have no sound `DeepModel`. |
| `AtomDomain::new_closed` | `domains/mod.rs` (trusted module) | On success, the closed bounds are `bounds`, and `lower <= upper`. | Generic comparisons in `Bounds::new`. |
| `VectorDomain::{new, with_size}` | `domains/mod.rs` | Field values. | Trivial. |
| `Bounds::eq`, `Column::eq` | `domains/mod.rs`, `data/mod.rs` | Consistent with an (opaque) deep model. | Carriers / type-erased columns have no `DeepModel`. |
| `Error::verified_new`, `err!` under Creusot | `error/mod.rs` | Builds an error with the given variant. | Message formatting and backtraces are not modeled; under Creusot, `err!` does not evaluate its message arguments. |
| `int_sum` | `transformations/sum/int/mod.rs` | If every prefix sum is representable, `iter().sum()` returns the exact sum. | `Iterator::sum` for integers adds in order. |
| `integer_real`, `integer_zero`, `integer_interval`, `integer_neg`, `integer_range`, `integer_in_range`, `integer_saturating_add` | `verification/integer.rs` | Facts about the values of `Integer` types: `real` is the integer value; values form the interval `[int_min, int_max]` containing 0 (with `int_min <= -int_max` if signed); `saturating_add` clamps to it. | Hold for each of the 12 integer types, the only implementors of `Integer`. Each integer `saturating_add` is itself verified against `std`'s specification. |
| `int_zero` | `transformations/sum/int/mod.rs` | `T::zero()` is 0. | `num::Zero` has no specification. |
| `StabilityMap::new_from_constant` | `core/mod.rs` | On success, `c >= 0` and `d_out >= d_in * c`. | Compares the generic distance `c` with zero. |
| `RealModel` for `f32`, `f64`, `FBig`, pairs | `verification/mod.rs` | Opaque. | Constrained only by trusted float contracts. Consistency is checked by mutation tests. |
| `DeepModel` for `IBig`, `UBig`, `RBig` | `creusot-std` fork | Opaque (`Int` / `Real`). | Not yet constrained by contracts. |

## Skipped (trusted without contracts)

- Modules outside the current scope: `accuracy`, `combinators`, `data`, `interactive`,
  `measurements`, `measures`, `utilities`, `error`, `domains`, `traits::{cast, operations, samplers}`,
  and every `transformations` submodule except `sum`.
- `PrivacyMap` methods, `Function::make_chain`, `StabilityMap::make_chain`,
  `PrivacyMap::new_from_constant`.
- Integer `alerting_pow`, `neg_inf_div` (no specifications for `checked_pow`,
  `num::Integer::div_floor`).
- `catch_unwind_silent`, float `ProductOrd::total_cmp`.
- Float sums: `round_up_to_nearest_power_of_two` (its contract is assumed by the Lean proof).
- Traits with self-referential associated types, moved into trusted modules (declarations only):
  `MicrodataMetric`/`EventLevelMetric`, `BoundedMetric`/`UnboundedMetric`, `ODPRound`.

## Proved in Lean

The Lean development (`verification/lean`) proves facts that Creusot cannot express or that need
a model of floating-point rounding. Its theorems depend only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). What they assume is stated as hypotheses:

| Theorem | Rust item | Assumed |
| --- | --- | --- |
| `OpenDP.Float.Fmt.canOverflowSeq_sound`, `canOverflowPw_sound` | `can_float_sum_overflow` (both impls), whose Creusot contract they justify | See below. |
| `OpenDP.Float.Fmt.satSeqSum_err` | `Sequential::<T>::saturating_sum`, justifying `seq_saturating_sum_error` | IEEE arithmetic and the transcription, as below; `saturating_add` is IEEE addition clamped to `[-MAX, MAX]` (an infinity clamps to `±MAX`). |

Assumptions of these theorems:

- **Transcription.** `canOverflowSeq`, `canOverflowPw`, `seqSum`, `pwSum` and `satSeqSum`
  transcribe the Rust code by hand (Aeneas cannot extract float code). They are short and mirror
  it line by line.
- **IEEE arithmetic.** `f32`/`f64` addition rounds to nearest, ties to even, and overflows to an
  infinity when the rounded result exceeds `MAX` (IEEE 754 binary32/binary64, as Rust specifies).
- **Primitive contracts** (`Prims.Spec`):
  - `inf_cast(size) >= size`;
  - `neg_inf_div` rounds down;
  - `inf_mul` rounds up *and returns `Err` on non-finite results* (implemented, but not part of
    its Proof Definition: see `FINDINGS.md` D3);
  - `powf(2, k) <= 2^k` (`_2.powf(...)`; the platform `pow` is exact on powers of two);
  - `round_up_to_nearest_power_of_two(x)` returns at least `2^c` for some `2^c >= x` with
    `c >= -emax` (from its bit manipulation and `inf_powi` rounding up).
- **Exact helpers.** `alerting_abs` and `total_max` are exact on floats (as in the Creusot
  contracts), and the bounds are not NaN (`mag` is then a real number).
- **Sizes.** `size < 2^64` (`usize`).
