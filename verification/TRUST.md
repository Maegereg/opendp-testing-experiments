# Trust table

Everything the proofs assume rather than prove. A trusted item *without* a contract is merely
skipped: nothing about it is assumed, so verified code cannot rely on its behavior. A trusted item
*with* a contract is an assumption: the contract is believed, not checked.

## Assumptions (trusted contracts)

| Item | Location | Assumed | Justification |
| --- | --- | --- | --- |
| `Function::{new, new_fallible, eval, clone}` | `core/mod.rs` | The ghost model (`pre`, `post`) records / replays the contract of the wrapped closure. | The bodies only wrap and call the closure; Creusot cannot see through `dyn Fn`. |
| `StabilityMap::{new, new_fallible, eval, clone}`, `PrivacyMap::{new, new_fallible, eval, clone}` | `core/mod.rs` | As above (`post`); the closure must be total on values satisfying their type invariant. | As above. |
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
| `ProductOrd::total_max` | `traits/operations/mod.rs` | Returns one of its arguments, at least as large as both. | Calls `max_by`, whose comparator is a generic `FnOnce` without a specification. |
| Float `ProductOrd` (`total_cmp`, `ple_refl`; `ple`, `non_null` opaque) | `traits/operations/mod.rs` | `total_cmp` returns the order `ple` on non-null values (`Less` iff strictly below, ...); `ple` only relates non-null values, and is reflexive on them. | `ple` is IEEE `<=` and `non_null` is "not NaN"; floats have no sound `DeepModel`. The integer, `IBig`, `RBig` and pair impls are verified. |
| `ord_clone` | `transformations/clamp/proof.rs` | Cloning a `ProductOrd` value returns the same value. | As `number_clone`; `ProductOrd` is implemented by the primitive numbers, `IBig`, `RBig` and pairs of these. |
| `int_ple`, `float_ple` | `transformations/clamp/proof.rs` | For `Integer` types, `ple` is `<=` on the integer values. For `Float` types, a value `ple`-between two finite values is finite, and lies between them as a real. | The integer impls define `ple` this way (`impl_ProductOrd_for_ord`); for floats, `ple` is IEEE `<=`. Not stated generically. Used only to connect `make_clamp`'s output to `make_sum`'s input. |
| `Ordering::{is_lt, is_le, is_gt, is_ge}` | `verification/mod.rs` (`extern_spec!`) | Each compares with `Less` / `Greater`. | `std`'s definitions; creusot-std does not specify them. |
| `AtomDomain::new_closed` | `domains/mod.rs` (trusted module) | On success, the closed bounds are `bounds`, `lower <= upper`, and the domain excludes NaN (`has_nan` false). | Generic comparisons in `Bounds::new`; sets `nan: false`. |
| `AtomDomain::assert_non_nan`, `AtomDomain::has_nan` | `domains/mod.rs` (trusted module) | `has_nan` is opaque: whether the domain admits null values. `assert_non_nan` succeeds only if it does not. | Reads the private `nan` field. |
| `VectorDomain::{new, with_size}` | `domains/mod.rs` | Field values. | Trivial. |
| `Bounds::get_closed`, `Bounds::closed` | `domains/mod.rs` (trusted module) | On success, returns the bounds' closed model `closed()` (opaque); `AtomDomain::closed_bounds` is defined from it. | Matches on `Bound::Included`; `Bounds<T>` has no deep model. |
| `Shuffle::shuffle` for `Vec<T>`, `vec_reorders` | `traits/samplers/mod.rs` (trusted module) | On success, the new vector is a shuffle of the old one (`reorders`, uninterpreted), and a shuffle is a permutation (`vec_reorders`). | `SliceRandom::shuffle` swaps elements. `reorders` is established only by `shuffle`, so a contract that requires it fails if the code does not shuffle (the identity is a permutation, but not a shuffle). That a shuffle is *uniform*, so that every ordering is a possible output, is the Proof Definition of `Shuffle`, used to read `resized` as the support of `make_resize`'s output and in `shuffle_match`. |
| `number_clone` | `verification/cast_metric.rs` | Cloning a `Number` returns the same value. | `Number` is implemented by the primitive integers and floats, whose `clone` creusot-std specifies as `*self`; this cannot be stated for a generic `T`. |
| `shuffle_match` | `verification/cast_metric.rs` | If `x` and `y` are within symmetric distance `d`, every ordering of `x` has an ordering of `y` within insert-delete distance `d`. | Combinatorial, not mechanized: delete `x`'s extra elements, append `y`'s. That the matching is a bijection between orderings, so that uniform shuffles of `x` and `y` couple, is cited from the proof of `make_ordered_random` (Kind C). It turns the matching statement proved for `make_sum` under `SymmetricDistance` (`float_sym_shuffled_stable`) into stability of the randomized output. |
| `atom_clone` | `transformations/resize/proof.rs` | Cloning a `CheckAtom` value returns an equal value. | `CheckAtom` is implemented by the primitive numbers, `bool`, `char`, `String`, `&str`, `IBig`, `RBig` and pairs of floats, all of whose clones are equal; this cannot be stated for a generic `T`. |
| `perm_same` | `transformations/resize/proof.rs` | A permutation (`permutation_of`) has the same number of occurrences of every value (`same`). | `permutation_of` is Why3's `permut`, defined by equal occurrence counts; `same` is equality of `count`. The two counts are not related in Creusot's library. |
| Coupling of `make_resize`'s matchings | `transformations/resize/proof.rs` | Where both `x` and `y` are shuffled (`SymmetricDistance` to `InsertDeleteDistance`; both truncated from `SymmetricDistance`), the matchings constructed between their outputs extend to couplings of the uniform shuffles. | Not mechanized. Padded datasets `c a` and `c b` with `|a| = |b|` couple by applying the same random permutation of positions to both, which is what `reorder` constructs (Hamming distance `|a|`); truncations of shuffles are uniformly random ordered subsets, matched in the same way. Where one side is deterministic, the matchings proved in both directions are the coupling, and nothing is assumed. |
| `sample_uniform` | `transformations/impute/mod.rs` | Requires finite bounds with `lower < upper`; returns a finite value in `[lower, upper)`. | `rand` 0.7's `UniformFloat::new` asserts finite bounds and `lower < upper` (it panics otherwise, F5), and chooses its scale so that every sample is below `upper`; on a lack of entropy the code returns `lower`. That the sample is uniform is not used. |
| `is_nan`, `lt`, `is_finite` (impute), `finite_non_null` | `transformations/impute/{mod,proof}.rs` | `is_nan` is `!non_null`; `lt` is `<` on the reals for finite values; `is_finite` is `finite`; finite floats are non-null. | IEEE 754, with `non_null` and `finite` the ghost models of non-NaN and finite floats. |
| `AtomDomain::new_non_nan` | `domains/mod.rs` (trusted module) | The domain excludes NaN (`has_nan` false). | Sets `nan: false`. |
| Coupling of row-by-row relations (`EventModel::close_rel`) | `verification/rows.rs`, `verification/rows_rel.rs` | For a random row function, the matching proved (rows shared by `x` and `y` keep their outputs) is a coupling of the output distributions. | Not mechanized: the rows are processed independently, so giving shared rows the same sample is a coupling. The matching itself is proved for all four event-level metrics. |
| `Bounds::eq`, `Column::eq` | `domains/mod.rs`, `data/mod.rs` | Consistent with an (opaque) deep model. | Carriers / type-erased columns have no `DeepModel`. |
| `Error::verified_new`, `err!` under Creusot | `error/mod.rs` | Builds an error with the given variant. | Message formatting and backtraces are not modeled; under Creusot, `err!` does not evaluate its message arguments. |
| `int_sum` | `transformations/sum/int/mod.rs` | If every prefix sum is representable, `iter().sum()` returns the exact sum. | `Iterator::sum` for integers adds in order. |
| `integer_real`, `integer_zero`, `integer_interval`, `integer_neg`, `integer_range`, `integer_in_range`, `integer_saturating_add` | `verification/integer.rs` | Facts about the values of `Integer` types: `real` is the integer value; values form the interval `[int_min, int_max]` containing 0 (with `int_min <= -int_max` if signed); `saturating_add` clamps to it. | Hold for each of the 12 integer types, the only implementors of `Integer`. Each integer `saturating_add` is itself verified against `std`'s specification. |
| `int_zero` | `transformations/sum/int/mod.rs` | `T::zero()` is 0. | `num::Zero` has no specification. |
| `count_by_map` | `transformations/count/mod.rs` | Returns a map whose keys are exactly the values in the data (by deep model), each mapped to its number of occurrences saturated at `TV::MAX`. | `HashMap::{new, entry}` have no specifications in Creusot. Also assumes that `Eq` and `Hash` on the key type agree with equality of deep models, as they do for `Hashable` types (integers, `bool`, `char`, `String`). Each integer `saturating_add` is verified on its own, but not its use in the loop. |
| `StabilityMap::new_from_constant` | `core/mod.rs` | On success, `c >= 0` and `d_out >= d_in * c`. | Compares the generic distance `c` with zero. |
| `RealModel` for `f32`, `f64`, `FBig`, pairs | `verification/mod.rs` | Opaque. | Constrained only by trusted float contracts. Consistency is checked by mutation tests. |
| Event-level metric definitions (`EventModel::close`) | `verification/rows.rs` | Definitions, not assumptions, but they must match OpenDP's: symmetric distance (multisets), insert-delete distance (common subsequence), change-one distance (same size, symmetric distance at most `2 d`), Hamming distance (same size, differing positions). | Transcribed from the Proof Definitions in `metrics/mod.rs`. |
| `DeepModel` for `IBig`, `UBig`, `RBig`; `Sign` | `creusot-std` fork | Opaque (`Int` / `Real`); `Sign` is its own model. | Constrained by the `dashu` specifications below. |

### `make_laplace` (phase 1)

Privacy is a property of output distributions, which the logic does not model, so a measurement's
validity is the uninterpreted predicate `m_valid` (and `t_valid` for transformations,
`verification/privacy.rs`). Everything that gives these predicates meaning is assumed:

| Item | Location | Assumed | Justification |
| --- | --- | --- | --- |
| `laplace_mechanism` | `measurements/noise/distribution/laplace/proof.rs` | A privacy map bounding the loss by `0` at `d_in = 0`, by at least `d_in / scale` when `scale > 0`, and by infinity when `scale = 0`, meets `NoisePrivacyMap`'s Proof Definition for `ZExpFamily<1>`. | **Proved in Lean** (`OpenDP.Laplace.laplace_mechanism`, `verification/lean/OpenDPVerification/Laplace.lean`, phase 2). What remains trusted is the correspondence between the two models, a review point: the discrete Laplace mass `(1 - e^{-1/s}) / (1 + e^{-1/s}) e^{-|z|/s}` (proved there to sum to 1) and the point mass at 0 for `s = 0`, as in `ZExpFamily`'s Proof Definition; independent samples as the product mass; vectors within L1 distance `d` as equal-length integer vectors with `sum_i |x_i - x'_i| <= d` (as `l1_int`); max-divergence at most `o` as `P(S) <= e^o Q(S)` for every set `S`; an `f64` loss as its value when finite and as no bound when `+inf` (the map returns `0`, `+inf`, or `d / s` rounded up, never NaN or `-inf`). |
| `noise_function` | `measurements/noise/mod.rs` | The noise function adds independent samples of the distribution to each element (`adds_noise`). | **The samplers are not verified** (claim B, deferred). The closure applies `Sample::sample`, whose Proof Definition promises `shift + Z`; for `ZExpFamily<1>` this is `sample_discrete_laplace` (CKS20). |
| `noise_measurement_valid` | `verification/privacy.rs` | A measurement whose function adds noise from `rv` and whose map meets `NoisePrivacyMap`'s Proof Definition for `rv` is valid. | The definition of a valid measurement, given the two Proof Definitions. |
| `make_chain_mt`, `make_chain_pm` | `combinators/chain/mod.rs` | A valid transformation chained into a valid measurement is valid; post-processing a valid measurement is valid. | Cited (Kind C): OpenDP's chaining proofs and post-processing immunity. The code composes `dyn Fn` closures, which Creusot cannot see through. |
| `singleton_valid`, `float_to_bigint_valid`, `int_to_bigint_valid` | `verification/privacy.rs`, `measurements/noise/nature/{float,integer}/proof.rs` | Each transformation is valid given concrete stability statements: `[x]` has `L_p` distance `|x - y|`; the L1 distance between float vectors is read as `l1_close_float` (equal lengths, differing elements finite) and between integer vectors as `l1_int`; exact conversions preserve distances. | Definitions of `AbsoluteDistance` and `LpDistance` (review point). The stability statements themselves are proved. |
| `NoisePrivacyMap` for `ZExpFamily<2>` | `measurements/noise/distribution/gaussian/mod.rs` | Meets its Proof Definition. | Out of scope (Gaussian); its contract is the trait's. No Laplace claim depends on it. |
| `dashu` operations (`verification/dashu.rs`, `extern_spec!`) | `verification/dashu.rs` | Exact arithmetic on `IBig`/`UBig`/`RBig` (`+`, `-`, `*`, `/`, shifts, `into_parts`, `from_parts`, `sign`, `is_zero`, `clone`, conversions from `usize`, `IBig`, finite `f32`/`f64`); `/` truncates and `>>` rounds down; `dashu_facts`: a `UBig` is non-negative. | `dashu`'s documentation; the rounding of `>>` on negative values was checked by running it. |
| `float_grid`, `fclamp_facts`, `float_conversion_facts`, `number_conversion_facts`, `ibig_from_facts` | `verification/float.rs`, `measurements/noise/nature/{float,integer}/proof.rs` | Finite floats are integer multiples of `2^min_k` within `[-MAX, MAX]` (`min_k` is -1074 / -149); clamping to `[MIN, MAX]` is the identity on finite values and finite on non-NaN ones; `RBig::try_from` and `IBig::from` are exact on numbers. | IEEE 754 and `num`/`dashu` behavior, which generic code cannot see. |
| `get_min_k` | `measurements/noise/nature/float/utilities/mod.rs` | Returns `min_k` (`-EXPONENT_BIAS - MANTISSA_BITS + 1`). | Constant arithmetic on associated constants. |
| `zero_loss` | `measurements/noise/distribution/laplace/mod.rs` | `0.0` is finite with value 0. | Creusot does not translate float literals in specifications. |
| `InfCast` for `f32`, `f64` from `dashu` types | `traits/cast/mod.rs` | The trait contract, restated on the impls. | As the `InfCast` row above. |
| `AtomDomain::clone`, `VectorDomain::clone`, `AtomDomain::nan` | `domains/mod.rs` (trusted module) | Clones have equal (deep) models; `nan()` returns `has_nan`. | Hand-written field-by-field clones. |
| `Result::map_err` | `verification/mod.rs` (`extern_spec!`) | Maps `Err` through the closure, keeps `Ok`. | `std`'s definition; creusot-std does not specify it. |

### `make_laplace_threshold`

| Item | Location | Assumed | Justification |
| --- | --- | --- | --- |
| `laplace_threshold_mechanism` | `measurements/noise_threshold/distribution/laplace/proof.rs` | A privacy map whose outputs satisfy `threshold_bound` meets `NoiseThresholdPrivacyMap`'s Proof Definition for `ZExpFamily<1>`: `ε >= Δ1 / s` and `δ >= 1 - (1 - Pr[Z > T - Δ∞])^l0`, with `Δ1 = min(⌊l1⌋, ⌊li⌋ l0)`, `Δ∞ = min(⌊li⌋, Δ1)`, or `(0, 0)` when `Δ1 = 0`, or `δ >= 1`. | Cited (Kind C): Rogers (2023), Theorem 7, as adapted in OpenDP's `NoiseThresholdPrivacyMap_for_ZExpFamily1`, for the release rule `v + Z > T` and with zero values dropped (F7, F8). The stable keys are the vector Laplace mechanism (proved in Lean). |
| `noise_threshold_measurement_valid` | `verification/privacy.rs` | A measurement on maps whose function releases noise with thresholding (`adds_noise_threshold`) and whose map meets `NoiseThresholdPrivacyMap`'s Proof Definition is valid. | The definition of a valid measurement, given the two Proof Definitions. |
| `noise_threshold_function` | `measurements/noise_threshold/mod.rs` | The function drops zero values, adds independent samples of the distribution to the others, and keeps the pairs `is_beyond` accepts (`adds_noise_threshold`). | **The samplers are not verified** (as for `noise_function`). `HashMap` iteration has no specification; the ordering of a `HashMap` does not depend on insertion order. `is_beyond` is verified; the zero filter is checked only by a test. |
| `dlap_tail_gt`, `clap_tail_gt`, `tail_facts` | `measurements/noise_threshold/distribution/laplace/proof.rs` | Opaque tails `Pr[Z > t]` (discrete) and `Pr[C > t]` (continuous); the continuous tail bounds the discrete one for `t >= 0`; both are non-negative. | Proved in Lean (`Threshold.lean`: `continuous_ge_discrete`, `tailGt_nonneg`); `Pr[C > t] >= 0` is immediate. |
| `conservative_{discrete,continuous}_laplacian_tail_to_alpha` | `accuracy/tail_bounds/mod.rs` (trusted module) | On success, the scale is positive and the result is finite, at least the tail, and at most 1. | The Proof Definitions (the result does not underestimate `Pr[X > t]`), and the computed values `e^{-t/s} / (e^{1/s} + 1)`, `e^{-t/s} / 2` (rounded up) are at most 1 for `t >= 0`. |
| `joint_delta`, `min_one`, `f64_zero`, `f64_one` | `measurements/noise_threshold/distribution/laplace/mod.rs` | `1 - (1 - δ)^l0` rounded up; `min(x, 1)`; the constants `0.0` and `1.0`. | `neg_inf_sub` and `neg_inf_powi` round down and `inf_sub` rounds up; Creusot does not translate float literals in specifications. |
| `map_values` | `measurements/noise_threshold/nature/mod.rs` | Applies a function to every value of a `HashMap`, keeping the keys. | `HashMap::iter` and `collect` have no specifications; assumes `Eq` and `Hash` on the key type agree with equality of deep models (as `count_by_map`). |
| `int_to_bigint_map_valid`, `float_to_bigint_map_valid` | `measurements/noise_threshold/nature/proof.rs` | A map conversion that keeps the keys and converts each value exactly (integers) or rounds it (floats, with the per-key bound `map_rounding_stable`, proved), with the corresponding stability map, is valid under `L0PInfDistance<1, _>`. | The definition of `L0PInfDistance` (a missing key is the value 0, which both conversions map to 0): summing the per-key bounds over the at most `l0` differing keys. The output value domain is `AtomDomain::<IBig>::default()`. |
| `is_negative` | `measurements/noise_threshold/nature/float/mod.rs` | No precondition. | `num::Float::is_sign_negative`; its result only selects an error. |
| `dashu` operations (`IBig::into_parts`, `RBig::{floor, round}`, `UBig` `*`, `-`, `is_zero`, `Clone`, `From<UBig> for RBig`, `IBig::clone`) | `verification/dashu.rs` | Exact, as documented by `dashu`; `floor` rounds down; `round` has no stated property. | `dashu`'s documentation. |
| `NoiseThresholdPrivacyMap` for `ZExpFamily<2>`, `MakeNoiseThreshold` for `DiscreteGaussian`, `make_gaussian_threshold`, `make_noise_threshold` | `measurements/noise_threshold/distribution/` | The trait contracts (no claim for the Gaussian). | Out of scope (Gaussian, and the measure-generic entry point). |
| `then_saturating_cast_hashmap`, `then_deintegerize_hashmap` | `measurements/noise_threshold/nature/` | No contract. | Post-processing: any function preserves validity (`make_chain_pm`). |

## Skipped (trusted without contracts)

- Modules outside the current scope: `accuracy`, `data`, `interactive`, `measures`, `utilities`,
  `error`, `domains`, `traits::{cast, samplers}`, every `measurements` submodule except `noise`,
  every `combinators` submodule except `chain`, and every `transformations` submodule except
  `sum`, `count`, `cast_metric`, `clamp`, `manipulation` and `scalar_to_vector`.
- In `measurements::noise`: the Gaussian and geometric `make_noise` methods (whose `noise_claim`
  is `true`: no claim), `make_gaussian`, `make_geometric`, `make_noise`,
  `NoiseMeasure::new_distribution`, `Nature::new_distribution`, the `Sample` impls (the samplers),
  and the post-processing functions `then_deintegerize_vec`, `then_saturating_cast` and
  `then_index_or_default`.
- In `transformations::count`: every constructor except `make_count_by`.
- In `transformations::manipulation`: `make_row_by_row`, `make_identity`, `make_is_equal`,
  `make_is_null`.
- In `traits::operations`: the `FloatBits` methods, float `CheckNull::is_null`, `HashMap`'s
  `CollectionSize::size`, `option_min`, `max_by`, `min_by`, `ProductOrd::total_min`.
- In `combinators::chain`: `make_chain_mt`, `make_chain_pm`, `mismatch_error`, and the `>>` impls
  involving measurements or functions. In `transformations::cast_metric`: `make_metric_bounded`,
  `make_metric_unbounded`.
- `PrivacyMap` methods, `PrivacyMap::new_from_constant`.
- Integer `alerting_pow`, `neg_inf_div` (no specifications for `checked_pow`,
  `num::Integer::div_floor`).
- `catch_unwind_silent`.
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
| `OpenDP.NpClamp.Clamp.clamp_map`, `clamp_stable`, `clamp_no_nan`, `clamp_member`, `clamp_empty`, `clamp_true_norm`, `clamp_terminates`, and the counterexamples F9-F14 (about the code before the fixes) | `make_np_clamp` (Python, `python/src/opendp/extras/numpy/_make_np_clamp/`) | The numpy model and the transcription, below. |
| `OpenDP.FillNull.fill_member`, `fill_stable`, `fill_stable_scalar`, and the counterexamples F20 (`fill_nan_counterexample`) and F21 (`null_leak`, `null_leak_f64`) | `make_expr_fill_null` (`rust/src/transformations/make_stable_expr/expr_fill_null/`) | The Polars model, below. |
| `OpenDP.NpClamp.Exec.ClampQ.clamp_toRes`, `rowNormQ_toF`, `numpyPlan` | none: they tie an executable copy of the `make_np_clamp` model to the model, so tests can run it | Nothing. The oracle's input and output (`NpClampOracle.lean`) and the constructor's computations (`floorFloat`, the conversion of `origin`) are not proved; the conformance tests check them. |

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

Assumptions of the `make_expr_fill_null` theorems (`FillNull.lean`):

- **Polars' `fill_null`** is per row: the data value, or the fill value if the data is null; a
  scalar fill is repeated on every row. Tested against Polars 0.52 in `expr_fill_null/test.rs`
  (`test_fill_null_model_*`: random columns with NaN, infinities and nulls; column and scalar fills;
  row-by-row and aggregation contexts).
- **Types.** The model has one value type. Polars casts to the supertype (F19), which the model
  does not cover.
- **Contexts.** The constructor requires a row-by-row context for a column fill (assumed: each
  child expression is then a function of the row), and allows any context for a scalar fill (the
  output is then a function of each value of the data expression's output).
- **F21.** `clip` keeps NaN; `sum` adds along some tree (`Plan`), as in `NpClamp.lean`; the noise
  mechanism rounds NaN to 0 (`discretize_vec`).
- **Not verified with Creusot.** Creusot's toolchain cannot compile Polars (`polars-ops` uses
  `core::unicode` items that its nightly lacks), so the constructor's own logic is only tested.

Assumptions of the `make_np_clamp` theorems (`NpClamp.lean`):

- **Transcription.**
  - `Clamp.clamp` transcribes `_function` by hand:
    - `arg - origin`, then `nan_to_num`;
    - the `while (current_norm > norm).any()` loop (with fuel, to state termination);
    - `arg + origin`, with rows that fail the norm check replaced by `origin`.
  - `Clamp.clampV0` transcribes the code before the fixes, which the counterexamples are about.
  - `Clamp.memberNorm` transcribes the norm check of `array2_domain`'s member function.

  The transcription is tested, not proved. `NpClampExec.lean` is an executable copy of the model,
  proved equal to it (`ClampQ.clamp_toRes`). `verification/conformance/test_np_clamp.py` runs it and
  the code on the same inputs, and requires the same floats:
  - `make_np_clamp`'s function, on random inputs (with NaN, infinities, subnormals, large values,
    both layouts) and on the inputs of the findings;
  - the output domain's norm check, on rows at the boundary.

  Inputs the tests do not reach are not covered, nor are norms within a factor 2 of the largest
  float (F18). `verification/scripts/np_clamp_counterexamples.py` checks that each counterexample
  behaves the same in numpy, and `python/test/extras/test_clamp_numpy.py` tests each fix.
- **Constructor checks.** The checks in `make_np_clamp` are not modelled; the theorems take them as
  hypotheses:
  - the minimum norm (`TermHyp`, and the hypotheses of `slack_le`, which `min_norm_f64` and
    `min_norm_f32` derive from it);
  - float elements;
  - a finite `origin` in the data type.
- **numpy element-wise operations are IEEE operations.** `-`, `+`, `*`, `/`, `np.sqrt`, `np.abs`,
  `np.maximum` and `np.nan_to_num` on `float64` (or `float32`) arrays act on each element as IEEE 754
  operations, rounding to nearest with ties to even and overflowing to infinities (`F64`, over
  `Fmt.rne`). Signed zeros are not modelled.
- **numpy's norm.** `np.linalg.norm(x, ord=p, axis=1)` computes, per row:
  - `add.reduce(abs(x))` for `p = 1`;
  - `sqrt(add.reduce(x * x))` for `p = 2`.

  This is from numpy's `linalg/_linalg.py`.
- **numpy's summation order.** `add.reduce` sums each row along a binary tree that depends only on
  the row length (`Plan`). This holds for C-ordered arrays, as observed. The function makes its array
  C-ordered, and the domain's check runs on the output, which is C-ordered (F15). The theorems hold
  for every such tree, so the exact pairwise order does not matter.

  The element-wise operations, the norm formulas and the order are tested together: `test_norm`
  requires the model's norm with `numpyPlan` (numpy's `pairwise_sum`) to equal `np.linalg.norm` on
  random rows, for row lengths 0-19 and up to 1500, in both formats (numpy 2.5.4).
- **One format.**
  - The data, `origin` (converted to the data type) and the bound `norm_T` are in one format.
    `norm_T` is the largest value of the data type that is at most `norm`.
  - The domain's check computes in the precision of the array, and compares with `norm` exactly,
    so passing it with `norm_T` implies passing it with `norm` (F16, F17).
- **True norms** (`clamp_true_norm`): proved for origin zero. With another origin, the domain's
  check measures `out - origin` after one more rounding; that rounding is not bounded.
- **Domain.** The symmetric distance compares datasets as multisets of rows, with rows compared as
  values (NaN equal to NaN).
