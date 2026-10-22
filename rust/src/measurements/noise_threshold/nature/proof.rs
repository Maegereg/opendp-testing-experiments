//! Verification of the conversions of maps to integer values for the threshold mechanisms.
//!
//! Each conversion keeps the keys and maps each value on its own: exactly (integers), or by
//! rounding to the nearest multiple of `2^k` (floats). Under `L0PInfDistance`, a missing key is read
//! as the value 0, which both conversions map to 0. Per key, the converted values differ by
//! exactly as much (integers), or by at most `(|a - b| + step) / 2^k`, with `step = 2^k - 2^min_k`
//! (floats, `map_rounding_stable`, proved). Summed over the at most `l0` keys that differ, this
//! gives the stability maps; the summation is the trusted part (`int_to_bigint_map_valid`,
//! `float_to_bigint_map_valid`).
use creusot_std::{
    logic::{Int, real::Real},
    prelude::*,
};
use dashu::{integer::IBig, rational::RBig};

use crate::{
    core::Transformation,
    domains::{AtomDomain, MapDomain},
    measurements::nature::float::{
        abs_scale, elem_bound, fdist, grid_round, grid_step, grid_witness, iabs, round_lipschitz,
        rounds_to, step_facts,
    },
    metrics::{AbsoluteDistance, L0PInfDistance},
    traits::{Float, Hashable, Integer, Number},
    verification::{
        MaybeDeepModel, RealModel, dashu::pow2r, float::FloatModel, privacy::t_valid, real_abs,
    },
};

pub type MapToBigint<TK, TV, const P: usize, QI> = Transformation<
    MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
    L0PInfDistance<P, AbsoluteDistance<QI>>,
    MapDomain<AtomDomain<TK>, AtomDomain<IBig>>,
    L0PInfDistance<P, AbsoluteDistance<RBig>>,
>;

/// The rounding slack per key, `2^k - 2^min_k`, or 0 if rounding is exact.
#[logic(open)]
pub fn step<T: Float>(k: Int) -> Real {
    pearlite! { if k == T::min_k() { Real::from_int(0) } else { pow2r(k) - pow2r(T::min_k()) } }
}

/// A key present in only one map: rounding a finite value `a` gives `n` with
/// `|n| <= (|a| + 2^k - 2^min_k) / 2^k`, as for a key whose other value is 0.
#[logic]
#[requires(a.non_null() && a.finite() && rounds_to(a, n, k) && k >= T::min_k())]
#[ensures(Real::from_int(iabs(n.deep_model()))
    <= (real_abs(a.real()) + (pow2r(k) - pow2r(T::min_k()))) * pow2r(-k))]
pub fn absent_bound<T: Float>(a: T, n: IBig, k: Int) {
    pearlite! {
        let g = T::min_k();
        let m = grid_witness(a);
        let p = crate::verification::float::pow2(k - g);
        proof_assert!(grid_step(g, k));
        grid_round(a, n, k, m);
        round_lipschitz(m, 0, n.deep_model(), 0, p);
        let e = Real::from_int(iabs(n.deep_model()));
        let q = Real::from_int(iabs(m)) + Real::from_int(p) - Real::from_int(1);
        abs_scale(m, pow2r(g));
        proof_assert!(real_abs(a.real()) == Real::from_int(iabs(m)) * pow2r(g));
        proof_assert!(Real::from_int(iabs(n.deep_model()) * p) == e * Real::from_int(p));
        proof_assert!(e * Real::from_int(p) <= q);
        proof_assert!(real_abs(a.real()) + (pow2r(k) - pow2r(g)) == q * pow2r(g));
        proof_assert!(q * pow2r(g) * pow2r(-k) == q * pow2r(g - k));
        proof_assert!(e == e * Real::from_int(p) * pow2r(g - k));
        proof_assert!(e * Real::from_int(p) * pow2r(g - k) <= q * pow2r(g - k));
    }
}

/// Per key, rounding to multiples of `2^k` moves values by at most the rounding slack: for two
/// values (equal, or both finite), and for a value against a missing key (0).
#[logic(open)]
pub fn map_rounding_stable<T: Float>(k: Int) -> bool {
    pearlite! {
        (forall<a: T, b: T, n: IBig, n2: IBig>
            a.non_null() && b.non_null() && (a == b || (a.finite() && b.finite()))
            && rounds_to(a, n, k) && rounds_to(b, n2, k) ==>
            Real::from_int(iabs(n.deep_model() - n2.deep_model())) <= (fdist(a, b) + step::<T>(k)) * pow2r(-k))
        && (forall<a: T, n: IBig> a.non_null() && a.finite() && rounds_to(a, n, k) ==>
            Real::from_int(iabs(n.deep_model())) <= (real_abs(a.real()) + step::<T>(k)) * pow2r(-k))
    }
}

/// `map_rounding_stable` holds for `k >= min_k`.
#[logic]
#[requires(k >= T::min_k())]
#[ensures(result && map_rounding_stable::<T>(k))]
pub fn map_rounding_is_stable<T: Float>(k: Int) -> bool {
    pearlite! {
        proof_assert!(step_facts(k, T::min_k()));
        proof_assert!(forall<a: T, b: T, n: IBig, n2: IBig>
            a.non_null() && b.non_null() && (a == b || (a.finite() && b.finite()))
            && rounds_to(a, n, k) && rounds_to(b, n2, k) ==> elem_bound(a, b, n, n2, k));
        proof_assert!(forall<a: T, n: IBig> a.non_null() && a.finite() && rounds_to(a, n, k) ==> {
            absent_bound(a, n, k);
            true
        });
        true
    }
}

/// A transformation that converts the values of an integer map exactly, keeping the keys, and
/// whose stability map converts the distances exactly, is valid under `L0PInfDistance<1, _>`.
///
/// Trusted: the definition of `L0PInfDistance` (a missing key is the value 0): per key, the
/// converted values differ exactly as much as the input values, so the `L0`, `L1` and `L∞` norms
/// of the differences are unchanged. Every map with keys in the input's key domain and `IBig`
/// values is a member of the output domain (whose value domain is `AtomDomain::<IBig>::default()`).
#[trusted]
#[logic(opaque)]
#[requires(P == 1usize)]
#[requires(t.output_domain.key_domain.deep_model() == t.input_domain.key_domain.deep_model())]
#[requires(forall<x: std::collections::HashMap<TK, TV>> inv(x) ==> t.function.pre()[x])]
#[requires(forall<x: std::collections::HashMap<TK, TV>, e: crate::error::Error> !t.function.post()[x][Err(e)])]
#[requires(forall<x: std::collections::HashMap<TK, TV>, y: std::collections::HashMap<TK, IBig>>
    t.function.post()[x][Ok(y)] ==> forall<k: TK::DeepModelTy> y@.contains(k) == x@.contains(k)
        && (x@.contains(k) ==> Real::from_int(y@[k].deep_model()) == x@[k].real()))]
#[requires(forall<d: (u32, QI, QI), o: (u32, RBig, RBig)> t.stability_map.post()[d][Ok(o)] ==>
    o.0 == d.0 && o.1.deep_model() == d.1.real() && o.2.deep_model() == d.2.real())]
#[ensures(result && t_valid(t))]
pub fn int_to_bigint_map_valid<
    TK: Hashable + MaybeDeepModel,
    TV: Integer,
    const P: usize,
    QI: Number,
>(
    t: MapToBigint<TK, TV, P, QI>,
) -> bool {
    dead
}

/// A transformation that rounds the values of a non-NaN float map to multiples of `2^k`,
/// keeping the keys, and whose stability map adds the rounding slack (`l0` times to the L1
/// distance, once to the L∞ distance) before scaling by `2^-k`, is valid under
/// `L0PInfDistance<1, _>`.
///
/// Trusted: the definition of `L0PInfDistance` (a missing key is the value 0, which rounds to 0).
/// Keys whose values are equal round to equal integers. Each of the at most `l0` keys that differ,
/// with finite values within `L∞` distance `li`, rounds to integers within
/// `(|a - b| + step) / 2^k` (`map_rounding_stable`, proved, with `|a - 0| = |a|` for a missing
/// key); summing over them gives `(l1 + l0 step) / 2^k`. Members of the input domain have non-null
/// values; every map with keys in the input's key domain and `IBig` values is a member of the output
/// domain.
#[trusted]
#[logic(opaque)]
#[requires(P == 1usize)]
#[requires(!t.input_domain.value_domain.has_nan())]
#[requires(t.output_domain.key_domain.deep_model() == t.input_domain.key_domain.deep_model())]
#[requires(k >= TV::min_k() && map_rounding_stable::<TV>(k))]
#[requires(forall<x: std::collections::HashMap<TK, TV>> inv(x) ==> t.function.pre()[x])]
#[requires(forall<x: std::collections::HashMap<TK, TV>, e: crate::error::Error> !t.function.post()[x][Err(e)])]
#[requires(forall<x: std::collections::HashMap<TK, TV>, y: std::collections::HashMap<TK, IBig>>
    t.function.post()[x][Ok(y)] ==> forall<key: TK::DeepModelTy> y@.contains(key) == x@.contains(key)
        && (x@.contains(key) ==> rounds_to(x@[key], y@[key], k)))]
#[requires(forall<d: (u32, QI, QI), o: (u32, RBig, RBig)> t.stability_map.post()[d][Ok(o)] ==>
    o.0 == d.0
    && o.1.deep_model() == (d.1.real() + Real::from_int(d.0@) * step::<TV>(k)) * pow2r(-k)
    && o.2.deep_model() == (d.2.real() + step::<TV>(k)) * pow2r(-k))]
#[ensures(result && t_valid(t))]
pub fn float_to_bigint_map_valid<
    TK: Hashable + MaybeDeepModel,
    TV: Float,
    const P: usize,
    QI: Number,
>(
    t: MapToBigint<TK, TV, P, QI>,
    k: Int,
) -> bool {
    dead
}
