//! Verification of `make_bounded_float_ordered_sum` and `make_sized_bounded_float_ordered_sum`
//! with sequential summation.
//!
//! The function sums the data with saturating float addition, `clamp(a + b, MIN, MAX)`. With
//! sequential summation, the result is within `e` of the exact sum clamped at every step
//! (`csum`), where `e` bounds the rounding error (proved in Lean). The clamped sum is stable under
//! the insert-delete distance (`verification::clamped`), so
//! `|f(x) - f(y)| <= e + |csum(x) - csum(y)| + e <= e + d_in * sensitivity + e`.
//!
//! The constructors' contracts hold for pairwise summation too, but its stability theorem does
//! not: the pairwise saturating sum is not stable (`FINDINGS.md`, F2).
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};

use super::{SaturatingSum, Sequential, SumRelaxation};
use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{AbsoluteDistance, InsertDeleteDistance, IntDistance},
    traits::Float,
    verification::{
        RealModel,
        clamped::{bounded, csum, id_close, sized_csum_sensitivity, unsized_csum_sensitivity},
        float::{float_facts, float_in_bounds, mag, reals, unit_roundoff},
        real_abs,
    },
};

pub type FloatOrderedSum<T> = Transformation<
    VectorDomain<AtomDomain<T>>,
    InsertDeleteDistance,
    AtomDomain<T>,
    AbsoluteDistance<T>,
>;

/// The contract of `make_bounded_float_ordered_sum(size_limit, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn float_ordered_sum_contract<S: SaturatingSum>(
    t: FloatOrderedSum<S::Item>,
    size_limit: usize,
    bounds: (S::Item, S::Item),
) -> bool {
    pearlite! {
        t.input_domain.size == None
        // elements of the input domain lie within `bounds`
        && t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        // the function can be evaluated on any (valid) dataset,
        && (forall<x: Vec<S::Item>> inv(x) ==> t.function.pre()[x])
        // and returns the saturating sum of its first `size_limit` elements
        && (forall<x: Vec<S::Item>, r> t.function.post()[x][r] ==>
            r == Ok(S::saturating_sum_logic(
                x@.subsequence(0, if x@.len() <= size_limit@ { x@.len() } else { size_limit@ }))))
        // the stability map returns at least d_in * max(|lower|, upper) + 2 e,
        // where e bounds the rounding error of summing `size_limit` values
        && exists<e: Real>
            S::error_bound(size_limit@, Real::from_int(size_limit@) * mag(bounds.0.real(), bounds.1.real()), e)
            && forall<d: IntDistance, o: S::Item> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@) * mag(bounds.0.real(), bounds.1.real()) + e + e
    }
}

/// The contract of `make_sized_bounded_float_ordered_sum(size, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn sized_float_ordered_sum_contract<S: SaturatingSum>(
    t: FloatOrderedSum<S::Item>,
    size: usize,
    bounds: (S::Item, S::Item),
) -> bool {
    pearlite! {
        t.input_domain.size == Some(size)
        // elements of the input domain lie within `bounds`
        && t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        // the function can be evaluated on any (valid) dataset,
        && (forall<x: Vec<S::Item>> inv(x) ==> t.function.pre()[x])
        // and returns its saturating sum
        && (forall<x: Vec<S::Item>, r> t.function.post()[x][r] ==> r == Ok(S::saturating_sum_logic(x@)))
        // the stability map returns at least (d_in / 2) * (upper - lower) + 2 e,
        // where e bounds the rounding error of summing `size` values
        && exists<e: Real>
            S::error_bound(size@, Real::from_int(size@) * mag(bounds.0.real(), bounds.1.real()), e)
            && forall<d: IntDistance, o: S::Item> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@ / 2) * (bounds.1.real() - bounds.0.real()) + e + e
    }
}

/// The sequential saturating sum of finite values bounded by `m` is within `n^2 m u` of the
/// clamped exact sum.
///
/// Trusted: proved in Lean (`OpenDP.Float.Fmt.satSeqSum_err`), where `saturating_sum_logic` is
/// `satSeqSum`, `csum(_, MAX)` is `clampSeqSum` and `u` is `2 ^ -p`.
#[trusted]
#[logic(opaque)]
#[requires(forall<i> 0 <= i && i < x.len() ==> x[i].finite() && real_abs(x[i].real()) <= m)]
#[ensures(real_abs(Sequential::<T>::saturating_sum_logic(x).real() - csum(reals(x), T::max_finite()))
    <= Real::from_int(x.len()) * (Real::from_int(x.len()) * m) * unit_roundoff::<T>())]
pub fn seq_saturating_sum_error<T: Float>(x: Seq<T>, m: Real) {
    dead
}

/// The saturating sum of `x`, of at most `size` values within `bounds`, is within `e` of its
/// clamped exact sum.
#[logic]
#[requires(Sequential::<T>::error_bound(size@, Real::from_int(size@) * mag(bounds.0.real(), bounds.1.real()), e))]
#[requires(x.len() <= size@ && float_in_bounds(x, bounds))]
#[ensures(real_abs(Sequential::<T>::saturating_sum_logic(x).real() - csum(reals(x), T::max_finite())) <= e)]
#[ensures(bounded(reals(x), bounds.0.real(), bounds.1.real()))]
pub fn seq_saturating_error<T: Float>(size: usize, bounds: (T, T), e: Real, x: Seq<T>) {
    pearlite! {
        let m = mag(bounds.0.real(), bounds.1.real());
        proof_assert!(forall<i> 0 <= i && i < x.len() ==> x[i].finite() && real_abs(x[i].real()) <= m);
        seq_saturating_sum_error::<T>(x, m);
        proof_assert!(Real::from_int(0) <= m);
        Sequential::<T>::error_bound_mono(
            x.len(), size@, Real::from_int(x.len()) * m, Real::from_int(size@) * m, e);
        proof_assert!(forall<i> 0 <= i && i < x.len() ==> reals(x)[i] == x[i].real())
    }
}

/// The sequential saturating sums of two sequences of at most `n` values within `bounds`, within
/// insert-delete distance `d`, differ by at most `d * max(|lower|, upper) + 2 e`, where `e` bounds
/// the rounding error of summing `n` values.
#[logic]
#[requires(Sequential::<T>::error_bound(n@, Real::from_int(n@) * mag(bounds.0.real(), bounds.1.real()), e))]
#[requires(x.len() <= n@ && float_in_bounds(x, bounds))]
#[requires(y.len() <= n@ && float_in_bounds(y, bounds))]
#[requires(id_close(reals(x), reals(y), d))]
#[ensures(real_abs(Sequential::<T>::saturating_sum_logic(x).real() - Sequential::<T>::saturating_sum_logic(y).real())
    <= Real::from_int(d) * mag(bounds.0.real(), bounds.1.real()) + e + e)]
pub fn seq_saturating_sum_stable<T: Float>(
    n: usize,
    bounds: (T, T),
    e: Real,
    x: Seq<T>,
    y: Seq<T>,
    d: Int,
) {
    pearlite! {
        let (lo, hi) = bounds;
        let m = mag(lo.real(), hi.real());
        float_facts::<T>();
        seq_saturating_error::<T>(n, bounds, e, x);
        seq_saturating_error::<T>(n, bounds, e, y);
        proof_assert!(m >= -lo.real() && m >= hi.real() && m >= Real::from_int(0));
        unsized_csum_sensitivity(reals(x), reals(y), d, T::max_finite(), lo.real(), hi.real(), m)
    }
}

/// The sequential saturating sums of two sequences of `n` values within `bounds`, within
/// insert-delete distance `d`, differ by at most `(d / 2) * (upper - lower) + 2 e`, where `e`
/// bounds the rounding error of summing `n` values.
#[logic]
#[requires(Sequential::<T>::error_bound(n@, Real::from_int(n@) * mag(bounds.0.real(), bounds.1.real()), e))]
#[requires(bounds.0.real() <= bounds.1.real())]
#[requires(x.len() == n@ && float_in_bounds(x, bounds))]
#[requires(y.len() == n@ && float_in_bounds(y, bounds))]
#[requires(id_close(reals(x), reals(y), d))]
#[ensures(real_abs(Sequential::<T>::saturating_sum_logic(x).real() - Sequential::<T>::saturating_sum_logic(y).real())
    <= Real::from_int(d / 2) * (bounds.1.real() - bounds.0.real()) + e + e)]
pub fn sized_seq_saturating_sum_stable<T: Float>(
    n: usize,
    bounds: (T, T),
    e: Real,
    x: Seq<T>,
    y: Seq<T>,
    d: Int,
) {
    pearlite! {
        let (lo, hi) = bounds;
        float_facts::<T>();
        seq_saturating_error::<T>(n, bounds, e, x);
        seq_saturating_error::<T>(n, bounds, e, y);
        proof_assert!(reals(x).len() == reals(y).len());
        sized_csum_sensitivity(reals(x), reals(y), d, T::max_finite(), lo.real(), hi.real())
    }
}

/// Stability of `make_sized_bounded_float_ordered_sum::<Sequential<T>>`: on any two datasets in
/// the input domain within insert-delete distance `d`, the outputs differ by at most the
/// stability map at `d`.
#[logic(prophetic)]
#[requires(sized_float_ordered_sum_contract::<Sequential<T>>(t, size, bounds))]
#[requires(x@.len() == size@ && float_in_bounds(x@, bounds))]
#[requires(y@.len() == size@ && float_in_bounds(y@, bounds))]
#[requires(id_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn sized_float_ordered_sum_is_stable<T: Float>(
    t: FloatOrderedSum<T>,
    size: usize,
    bounds: (T, T),
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    sx: T,
    sy: T,
    o: T,
) -> bool {
    pearlite! {
        let (lo, hi) = bounds;
        let e = such_that(|e: Real|
            Sequential::<T>::error_bound(size@, Real::from_int(size@) * mag(lo.real(), hi.real()), e)
            && forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@ / 2) * (hi.real() - lo.real()) + e + e);
        sized_seq_saturating_sum_stable::<T>(size, bounds, e, x@, y@, d@);
        true
    }
}

/// Stability of `make_bounded_float_ordered_sum::<Sequential<T>>`: on any two datasets in the
/// input domain of at most `size_limit` values, within insert-delete distance `d`, the outputs
/// differ by at most the stability map at `d`.
///
/// Larger datasets are truncated to their first `size_limit` values, which is not covered here.
#[logic(prophetic)]
#[requires(float_ordered_sum_contract::<Sequential<T>>(t, size_limit, bounds))]
#[requires(x@.len() <= size_limit@ && float_in_bounds(x@, bounds))]
#[requires(y@.len() <= size_limit@ && float_in_bounds(y@, bounds))]
#[requires(id_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn float_ordered_sum_is_stable<T: Float>(
    t: FloatOrderedSum<T>,
    size_limit: usize,
    bounds: (T, T),
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    sx: T,
    sy: T,
    o: T,
) -> bool {
    pearlite! {
        let (lo, hi) = bounds;
        let m = mag(lo.real(), hi.real());
        let e = such_that(|e: Real|
            Sequential::<T>::error_bound(size_limit@, Real::from_int(size_limit@) * m, e)
            && forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@) * m + e + e);
        proof_assert!(x@.subsequence(0, x@.len()) == x@ && y@.subsequence(0, y@.len()) == y@);
        seq_saturating_sum_stable::<T>(size_limit, bounds, e, x@, y@, d@);
        true
    }
}
