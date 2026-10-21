//! Verification of `make_bounded_float_checked_sum` and `make_sized_bounded_float_checked_sum`.
//!
//! The function sums the data in floating-point arithmetic. Each sum is within `e` of the exact
//! sum, where `e` bounds the rounding error (`SumRelaxation::error_bound`), provided that it does
//! not overflow (`CanFloatSumOverflow::sum_finite`), which the constructor checks. So
//! `|f(x) - f(y)| <= |f(x) - sum(x)| + |sum(x) - sum(y)| + |sum(y) - f(y)|
//! <= e + d_in * sensitivity + e`, and the stability map returns at least this.
use creusot_std::{
    logic::{real::Real, such_that},
    prelude::*,
};

use super::UncheckedSum;
use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{AbsoluteDistance, IntDistance, SymmetricDistance},
    verification::{
        RealModel,
        dataset::{sized_sum_sensitivity, sum, sym_close, unsized_sum_sensitivity},
        float::{abs_sum, abs_sum_bound, float_in_bounds, mag, reals},
        real_abs,
    },
};

pub type FloatSum<T> = Transformation<
    VectorDomain<AtomDomain<T>>,
    SymmetricDistance,
    AtomDomain<T>,
    AbsoluteDistance<T>,
>;

/// `s` is a float sum of `x`: if the sum does not overflow, `s` is within any bound `e` on the
/// rounding error of the exact sum.
#[logic(open, inline)]
pub fn float_sum_of<S: UncheckedSum>(x: Seq<S::Item>, s: S::Item) -> bool {
    pearlite! {
        forall<e: Real> S::sum_finite(x) && S::error_bound(x.len(), abs_sum(reals(x)), e) ==>
            real_abs(s.real() - sum(reals(x))) <= e
    }
}

/// The parts of the contracts shared by both constructors.
#[logic(open, prophetic, inline)]
pub fn float_checked_sum_common<S: UncheckedSum>(
    t: FloatSum<S::Item>,
    size: usize,
    bounds: (S::Item, S::Item),
) -> bool {
    pearlite! {
        // elements of the input domain lie within `bounds`
        t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        // summing at most `size` values within `bounds` does not overflow
        && (forall<x: Seq<S::Item>> x.len() <= size@ && float_in_bounds(x, bounds) ==> S::sum_finite(x))
        // the function can be evaluated on any (valid) dataset
        && (forall<x: Vec<S::Item>> inv(x) ==> t.function.pre()[x])
    }
}

/// The contract of `make_bounded_float_checked_sum(size_limit, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn float_checked_sum_contract<S: UncheckedSum>(
    t: FloatSum<S::Item>,
    size_limit: usize,
    bounds: (S::Item, S::Item),
) -> bool {
    pearlite! {
        t.input_domain.size == None
        && float_checked_sum_common::<S>(t, size_limit, bounds)
        // on datasets of at most `size_limit` values, the function returns their float sum
        && (forall<x: Vec<S::Item>, r> x@.len() <= size_limit@ && t.function.post()[x][r] ==>
            exists<s: S::Item> r == Ok(s) && float_sum_of::<S>(x@, s))
        // the stability map returns at least d_in * max(|lower|, upper) + 2 e,
        // where e bounds the rounding error of summing `size_limit` values
        && exists<e: Real>
            S::error_bound(size_limit@, Real::from_int(size_limit@) * mag(bounds.0.real(), bounds.1.real()), e)
            && forall<d: IntDistance, o: S::Item> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@) * mag(bounds.0.real(), bounds.1.real()) + e + e
    }
}

/// The contract of `make_sized_bounded_float_checked_sum(size, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn sized_float_checked_sum_contract<S: UncheckedSum>(
    t: FloatSum<S::Item>,
    size: usize,
    bounds: (S::Item, S::Item),
) -> bool {
    pearlite! {
        t.input_domain.size == Some(size)
        && float_checked_sum_common::<S>(t, size, bounds)
        // the function returns the float sum of the dataset
        && (forall<x: Vec<S::Item>, r> t.function.post()[x][r] ==>
            exists<s: S::Item> r == Ok(s) && float_sum_of::<S>(x@, s))
        // the stability map returns at least (d_in / 2) * (upper - lower) + 2 e,
        // where e bounds the rounding error of summing `size` values
        && exists<e: Real>
            S::error_bound(size@, Real::from_int(size@) * mag(bounds.0.real(), bounds.1.real()), e)
            && forall<d: IntDistance, o: S::Item> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@ / 2) * (bounds.1.real() - bounds.0.real()) + e + e
    }
}

/// The float sum of `x`, of at most `size` values within `bounds`, is within `e` of its exact sum.
#[logic]
#[requires(forall<y: Seq<S::Item>> y.len() <= size@ && float_in_bounds(y, bounds) ==> S::sum_finite(y))]
#[requires(S::error_bound(size@, Real::from_int(size@) * mag(bounds.0.real(), bounds.1.real()), e))]
#[requires(x.len() <= size@ && float_in_bounds(x, bounds))]
#[requires(float_sum_of::<S>(x, s))]
#[ensures(real_abs(s.real() - sum(reals(x))) <= e)]
#[ensures(forall<i> 0 <= i && i < x.len() ==>
    bounds.0.real() <= reals(x)[i] && reals(x)[i] <= bounds.1.real())]
pub fn float_sum_error<S: UncheckedSum>(
    size: usize,
    bounds: (S::Item, S::Item),
    e: Real,
    x: Seq<S::Item>,
    s: S::Item,
) {
    pearlite! {
        abs_sum_bound(x, bounds);
        let m = mag(bounds.0.real(), bounds.1.real());
        proof_assert!(Real::from_int(x.len()) * m <= Real::from_int(size@) * m);
        S::error_bound_mono(x.len(), size@, abs_sum(reals(x)), Real::from_int(size@) * m, e)
    }
}

/// Stability of `make_sized_bounded_float_checked_sum`: on any two datasets in the input domain
/// within symmetric distance `d`, the outputs differ by at most the stability map at `d`.
#[logic(prophetic)]
#[requires(sized_float_checked_sum_contract::<S>(t, size, bounds))]
#[requires(x@.len() == size@ && float_in_bounds(x@, bounds))]
#[requires(y@.len() == size@ && float_in_bounds(y@, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn sized_float_checked_sum_is_stable<S: UncheckedSum>(
    t: FloatSum<S::Item>,
    size: usize,
    bounds: (S::Item, S::Item),
    x: Vec<S::Item>,
    y: Vec<S::Item>,
    d: IntDistance,
    sx: S::Item,
    sy: S::Item,
    o: S::Item,
) -> bool {
    pearlite! {
        let (lo, hi) = bounds;
        let e = such_that(|e: Real|
            S::error_bound(size@, Real::from_int(size@) * mag(lo.real(), hi.real()), e)
            && forall<d: IntDistance, o: S::Item> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@ / 2) * (hi.real() - lo.real()) + e + e);
        float_sum_error::<S>(size, bounds, e, x@, sx);
        float_sum_error::<S>(size, bounds, e, y@, sy);
        sized_sum_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real());
        true
    }
}

/// Stability of `make_bounded_float_checked_sum`: on any two datasets in the input domain of at
/// most `size_limit` values, within symmetric distance `d`, the outputs differ by at most the
/// stability map at `d`.
///
/// Larger datasets are shuffled and truncated to `size_limit` values. The function is then
/// randomized, and its stability is not covered here.
#[logic(prophetic)]
#[requires(float_checked_sum_contract::<S>(t, size_limit, bounds))]
#[requires(x@.len() <= size_limit@ && float_in_bounds(x@, bounds))]
#[requires(y@.len() <= size_limit@ && float_in_bounds(y@, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn float_checked_sum_is_stable<S: UncheckedSum>(
    t: FloatSum<S::Item>,
    size_limit: usize,
    bounds: (S::Item, S::Item),
    x: Vec<S::Item>,
    y: Vec<S::Item>,
    d: IntDistance,
    sx: S::Item,
    sy: S::Item,
    o: S::Item,
) -> bool {
    pearlite! {
        let (lo, hi) = bounds;
        let m = mag(lo.real(), hi.real());
        let e = such_that(|e: Real|
            S::error_bound(size_limit@, Real::from_int(size_limit@) * m, e)
            && forall<d: IntDistance, o: S::Item> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@) * m + e + e);
        float_sum_error::<S>(size_limit, bounds, e, x@, sx);
        float_sum_error::<S>(size_limit, bounds, e, y@, sy);
        unsized_sum_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real(), m);
        true
    }
}
