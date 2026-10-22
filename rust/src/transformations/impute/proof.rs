//! Verification of `make_impute_uniform_float`.
//!
//! The row function replaces each NaN row with a uniform sample from `[lower, upper)` and keeps
//! the other rows. It is random, so it relates each row to its possible outputs (`imputed`) rather
//! than mapping it. Event-level distances are preserved by such relations
//! (`EventModel::close_rel`): matching rows keep their outputs, which is the coupling that gives
//! them the same sample.
use creusot_std::{logic::Mapping, prelude::*};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{EventLevelMetric, IntDistance},
    traits::Float,
    verification::{RealModel, float::FloatModel, rows::EventModel},
};

pub type Impute<TA, M> =
    Transformation<VectorDomain<AtomDomain<TA>>, M, VectorDomain<AtomDomain<TA>>, M>;

/// Finite floats are not NaN.
///
/// Trusted: `finite` and `non_null` are the ghost models of finite and non-NaN floats.
#[trusted]
#[logic(opaque)]
#[ensures(result && forall<v: T> v.finite() ==> v.non_null())]
pub fn finite_non_null<T: Float>() -> bool {
    dead
}

/// `w` is a possible output of the row function on `v`: `v` itself if it is not NaN, and otherwise
/// a finite value in `[lower, upper)`.
#[logic(open)]
pub fn imputed<T: Float>(v: T, w: T, lower: T, upper: T) -> bool {
    pearlite! {
        if v.non_null() {
            w == v
        } else {
            w.finite() && lower.real() <= w.real() && w.real() < upper.real()
        }
    }
}

/// `imputed`, as a relation on pairs.
#[logic(open)]
pub fn imputer<T: Float>(lower: T, upper: T) -> Mapping<(T, T), bool> {
    pearlite! { |p: (T, T)| imputed(p.0, p.1, lower, upper) }
}

/// An output of the row function on every row: `lower` for NaN rows.
#[logic(open)]
pub fn impute_lower<T: Float>(lower: T) -> Mapping<T, T> {
    pearlite! { |v: T| if v.non_null() { v } else { lower } }
}

/// The contract of `make_impute_uniform_float` on success.
#[logic(open, prophetic)]
pub fn impute_uniform_contract<TA: Float, M: EventLevelMetric>(
    t: Impute<TA, M>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    bounds: (TA, TA),
) -> bool {
    pearlite! {
        let (lower, upper) = bounds;
        // the bounds are finite, with `lower < upper`,
        lower.finite() && upper.finite() && lower.real() < upper.real()
        // the output domain excludes NaN, and keeps the input's size,
        && !t.output_domain.element_domain.has_nan()
        && t.output_domain.size == input_domain.size
        // the function can be evaluated on any dataset,
        && (forall<x: Vec<TA>> inv(x) ==> t.function.pre()[x])
        // imputes each row, with no NaN in the output,
        && (forall<x: Vec<TA>, y: Vec<TA>> t.function.post()[x][Ok(y)] ==>
            y@.len() == x@.len()
            && forall<i> 0 <= i && i < x@.len() ==> imputed(x@[i], y@[i], lower, upper) && y@[i].non_null())
        // never fails,
        && (forall<x: Vec<TA>, r: Fallible<Vec<TA>>> t.function.post()[x][r] ==> exists<y: Vec<TA>> r == Ok(y))
        // and the stability map returns at least d_in
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= d@)
    }
}

/// Stability of `make_impute_uniform_float` under any event-level metric `M`: for `d`-close `x`
/// and `y`, every possible output of `x` is matched with a possible output of `y` within the map.
#[logic(prophetic)]
#[requires(impute_uniform_contract(t, input_domain, bounds))]
#[requires(M::close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(fx)] && t.stability_map.post()[d][Ok(o)])]
#[ensures(result.len() == y@.len()
    && forall<j> 0 <= j && j < y@.len() ==> imputed(y@[j], result[j], bounds.0, bounds.1))]
#[ensures(M::close(fx@, result, o@))]
pub fn impute_uniform_stable<TA: Float, M: EventLevelMetric>(
    t: Impute<TA, M>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    bounds: (TA, TA),
    x: Vec<TA>,
    y: Vec<TA>,
    d: IntDistance,
    fx: Vec<TA>,
    o: IntDistance,
) -> Seq<TA> {
    pearlite! {
        let (lower, upper) = bounds;
        let r = imputer(lower, upper);
        let fy = M::close_rel(x@, y@, d@, r, impute_lower(lower), fx@);
        M::close_mono(fx@, fy, d@, o@);
        fy
    }
}

use crate::error::Fallible;
