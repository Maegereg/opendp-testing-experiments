//! Verification of `make_clamp`.
//!
//! The function clamps each row into the bounds, so it maps rows by the same (logical) function
//! `clamper(bounds)`. Every event-level metric is preserved by such maps (`EventModel::close_map`),
//! so the transformation is stable with the map `d -> d`. Its outputs lie within the bounds
//! in the order of `ProductOrd`, which for integers and finite floats is the order of the
//! (real) values that `make_sum` assumes of its inputs (`clamp_int_bounded`, `clamp_float_bounded`).
use creusot_std::{logic::Mapping, prelude::*};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    error::Fallible,
    metrics::{EventLevelMetric, IntDistance},
    traits::{CheckAtom, Float, Integer, ProductOrd, clamp_log},
    verification::{float::float_in_bounds, ordered::bounded},
};

pub type Clamp<TA, M> =
    Transformation<VectorDomain<AtomDomain<TA>>, M, VectorDomain<AtomDomain<TA>>, M>;

/// Cloning an ordered value copies it.
///
/// Trusted: `ProductOrd` is implemented by the primitive numbers (whose `clone` creusot-std
/// specifies as `*self`), by `IBig` and `RBig`, and by pairs of these, all of whose clones are
/// equal to the original. This cannot be stated for a generic `T`.
#[trusted]
#[logic(opaque)]
#[ensures(result && forall<a: T, b: T> T::clone.postcondition((&a,), b) ==> a == b)]
pub fn ord_clone<T: ProductOrd + Clone>() -> bool {
    dead
}

/// Clamping to `[lower, upper]`, as a logical function on rows.
#[logic(open)]
pub fn clamper<TA: ProductOrd>(lower: TA, upper: TA) -> Mapping<TA, TA> {
    pearlite! { |v| clamp_log(v, lower, upper) }
}

/// The contract of `make_clamp` on success.
#[logic(open, prophetic)]
pub fn clamp_contract<TA: Clone + ProductOrd + PartialOrd + CheckAtom, M: EventLevelMetric>(
    t: Clamp<TA, M>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    bounds: (TA, TA),
) -> bool {
    pearlite! {
        // the input domain excludes null values,
        t.input_domain == input_domain && !input_domain.element_domain.has_nan()
        // the output domain holds non-null rows within the (ordered) bounds, and the same sizes,
        && bounds.0.ple(bounds.1)
        && t.output_domain.element_domain.closed_bounds() == Some(bounds)
        && !t.output_domain.element_domain.has_nan()
        && t.output_domain.size == input_domain.size
        // the function can be evaluated on any dataset,
        && (forall<x: Vec<TA>> inv(x) ==> t.function.pre()[x])
        // clamps each row into the bounds,
        && (forall<x: Vec<TA>, y: Vec<TA>> t.function.post()[x][Ok(y)] ==>
            y@ == x@.map(clamper(bounds.0, bounds.1))
            && forall<i> 0 <= i && i < y@.len() ==> bounds.0.ple(y@[i]) && y@[i].ple(bounds.1))
        // and, if any two non-null values of `TA` are comparable, succeeds on non-null data
        && (TA::total() ==> forall<x: Vec<TA>, r: Fallible<Vec<TA>>> t.function.post()[x][r]
            && (forall<i> 0 <= i && i < x@.len() ==> x@[i].non_null())
            ==> exists<y: Vec<TA>> r == Ok(y))
        // the stability map returns at least d_in
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= d@)
    }
}

/// Stability of `make_clamp`: on any two datasets within distance `d`, the clamped datasets are
/// within the stability map at `d`, under any event-level metric.
#[logic(prophetic)]
#[requires(clamp_contract(t, input_domain, bounds))]
#[requires(M::close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(fx)] && t.function.post()[y][Ok(fy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(M::close(fx@, fy@, o@))]
pub fn clamp_is_stable<TA: Clone + ProductOrd + PartialOrd + CheckAtom, M: EventLevelMetric>(
    t: Clamp<TA, M>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    bounds: (TA, TA),
    x: Vec<TA>,
    y: Vec<TA>,
    d: IntDistance,
    fx: Vec<TA>,
    fy: Vec<TA>,
    o: IntDistance,
) {
    pearlite! {
        let f = clamper(bounds.0, bounds.1);
        M::close_map(x@, y@, d@, f);
        M::close_mono(x@.map(f), y@.map(f), d@, o@);
    }
}

/// The order of an integer type is the order of the integers.
///
/// Trusted: `Integer` is implemented by the primitive integers, whose `ple` is defined as
/// `self@ <= other@` (`impl_ProductOrd_for_ord`). This cannot be stated for a generic `T`.
#[trusted]
#[logic(opaque)]
#[ensures(forall<a: T, b: T> a.ple(b) == (a.deep_model() <= b.deep_model()))]
pub fn int_ple<T: Integer>() {
    dead
}

/// Between finite bounds, the order of a float type is the order of the reals.
///
/// Trusted: `ple` is IEEE `<=` on `f32` and `f64` (the only `Float` types), and a float that
/// lies between two finite floats is finite.
#[trusted]
#[logic(opaque)]
#[ensures(forall<lo: T, v: T, hi: T> lo.finite() && hi.finite() && lo.ple(v) && v.ple(hi) ==>
    v.finite() && lo.real() <= v.real() && v.real() <= hi.real())]
pub fn float_ple<T: Float>() {
    dead
}

/// Clamped integers lie within the bounds, as the integer sums of `make_sum` assume.
#[logic(prophetic)]
#[requires(clamp_contract(t, input_domain, bounds))]
#[requires(t.function.post()[x][Ok(fx)])]
#[ensures(bounded(fx@, bounds.0.deep_model(), bounds.1.deep_model()))]
pub fn clamp_int_bounded<T: Integer, M: EventLevelMetric>(
    t: Clamp<T, M>,
    input_domain: VectorDomain<AtomDomain<T>>,
    bounds: (T, T),
    x: Vec<T>,
    fx: Vec<T>,
) {
    int_ple::<T>()
}

/// Floats clamped to finite bounds are finite and lie within the bounds, as the float sums of
/// `make_sum` assume.
#[logic(prophetic)]
#[requires(clamp_contract(t, input_domain, bounds))]
#[requires(bounds.0.finite() && bounds.1.finite())]
#[requires(t.function.post()[x][Ok(fx)])]
#[ensures(float_in_bounds(fx@, bounds))]
#[ensures(bounds.0.real() <= bounds.1.real())]
pub fn clamp_float_bounded<T: Float, M: EventLevelMetric>(
    t: Clamp<T, M>,
    input_domain: VectorDomain<AtomDomain<T>>,
    bounds: (T, T),
    x: Vec<T>,
    fx: Vec<T>,
) {
    pearlite! {
        float_ple::<T>();
        proof_assert!(T::ple_refl(bounds.0, bounds.1));
    }
}
