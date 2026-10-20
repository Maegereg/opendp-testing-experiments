# Trust table

Everything the proofs assume rather than prove. A trusted item *without* a contract is merely
skipped: nothing about it is assumed, so verified code cannot rely on its behavior. A trusted item
*with* a contract is an assumption: the contract is believed, not checked.

## Assumptions (trusted contracts)

| Item | Location | Assumed | Justification |
| --- | --- | --- | --- |
| `Function::{new, new_fallible, eval, clone}` | `core/mod.rs` | The ghost model (`pre`, `post`) records / replays the contract of the wrapped closure. | The bodies only wrap and call the closure; Creusot cannot see through `dyn Fn`. |
| `StabilityMap::{new, new_fallible, eval, clone}` | `core/mod.rs` | As above (`post`); the closure must be total. | As above. |
| Float `Inf{Add,Sub,Mul,Div}`, `AlertingAbs`, `Alerting*`, `Saturating*`, `Inf{Ln,Log2,Exp,...}`, `InfPowI` | `traits/arithmetic/mod.rs` | The trait contracts (e.g. `inf_add`: `out >= self + v`). | Implemented with `dashu` arbitrary-precision floats; not verifiable in Creusot. Candidate for testing / Kani. |
| Signed integer `alerting_abs` | `traits/arithmetic/mod.rs` | `out = |self|`. | Wraps `checked_abs`, which `creusot-std` does not specify. |
| `InfCast`, `ExactIntCast` (all impls) | `traits/cast/mod.rs` (trusted module) | `inf_cast`: `out >= v`; `neg_inf_cast`: `out <= v`; `exact_int_cast`: `out = v`. | Module includes float casts Creusot cannot translate. Integer-to-integer impls could be verified. |
| `ProductOrd::total_max` | `traits/operations/mod.rs` (trusted module) | Returns one of its arguments, at least as large as both. | Generic comparisons; floats have no sound `DeepModel`. |
| `AtomDomain::new_closed` | `domains/mod.rs` (trusted module) | On success, the closed bounds are `bounds`, and `lower <= upper`. | Generic comparisons in `Bounds::new`. |
| `VectorDomain::{new, with_size}` | `domains/mod.rs` | Field values. | Trivial. |
| `Bounds::eq`, `Column::eq` | `domains/mod.rs`, `data/mod.rs` | Consistent with an (opaque) deep model. | Carriers / type-erased columns have no `DeepModel`. |
| `Error::verified_new`, `err!` under Creusot | `error/mod.rs` | Builds an error with the given variant. | Message formatting and backtraces are not modeled; under Creusot, `err!` does not evaluate its message arguments. |
| `int_sum` | `transformations/sum/int/mod.rs` | If every prefix sum is representable, `iter().sum()` returns the exact sum. | `Iterator::sum` for integers adds in order. |
| `integer_real`, `integer_zero`, `integer_interval`, `integer_neg` | `verification/integer.rs` | Facts about the values of `Integer` types. | Hold for each of the 12 integer types, the only implementors of `Integer`. |
| `RealModel` for `f32`, `f64`, `FBig`, pairs | `verification/mod.rs` | Opaque. | Constrained only by trusted float contracts. Consistency is checked by mutation tests. |
| `DeepModel` for `IBig`, `UBig`, `RBig` | `creusot-std` fork | Opaque (`Int` / `Real`). | Not yet constrained by contracts. |

## Skipped (trusted without contracts)

- Modules outside the current scope: `accuracy`, `combinators`, `data`, `interactive`,
  `measurements`, `measures`, `utilities`, `error`, `domains`, `traits::{cast, operations, samplers}`,
  and every `transformations` submodule except `sum`.
- `PrivacyMap` methods, `Function::make_chain`, `StabilityMap::make_chain`,
  `{Privacy,Stability}Map::new_from_constant`.
- Integer `alerting_pow`, `inf_div`, `neg_inf_div` (no specifications for `checked_pow`,
  `num::Integer::div_{ceil,floor}`).
- `catch_unwind_silent`, float `ProductOrd::total_cmp`.
- Float sums: `can_float_sum_overflow`, `round_up_to_nearest_power_of_two` (pending the float phase).
- Traits with self-referential associated types, moved into trusted modules (declarations only):
  `MicrodataMetric`/`EventLevelMetric`, `BoundedMetric`/`UnboundedMetric`, `ODPRound`.
