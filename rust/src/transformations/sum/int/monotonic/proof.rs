//! Verification of `make_bounded_int_monotonic_sum` and `make_sized_bounded_int_monotonic_sum`.
//!
//! Both sum with saturating arithmetic. Since the bounds share a sign, every element does too,
//! so the saturating sum is the exact sum clamped to the range of `T` (`monotone_sat_sum`), and
//! clamping cannot increase the distance between sums (`clamp_lipschitz`).
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{AbsoluteDistance, IntDistance, SymmetricDistance},
    traits::Integer,
    verification::{
        dataset::{sized_sum_sensitivity, sum, sym_close, unsized_sum_sensitivity},
        integer::{
            clamp, clamp_lipschitz, integer_real, isum, isum_real, monotone_sat_sum, real_bounds,
            reals, sat_sum,
        },
        real_abs,
    },
};

pub type IntSum<T> = Transformation<
    VectorDomain<AtomDomain<T>>,
    SymmetricDistance,
    AtomDomain<T>,
    AbsoluteDistance<T>,
>;

/// The parts of the contracts shared by both constructors.
#[logic(open, prophetic, inline)]
pub fn int_monotonic_sum_common<T: Integer>(t: IntSum<T>, bounds: (T, T)) -> bool {
    pearlite! {
        // elements of the input domain lie within `bounds`, which share a sign
        t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        && ((bounds.0.deep_model() >= 0 && bounds.1.deep_model() >= 0)
            || (bounds.0.deep_model() <= 0 && bounds.1.deep_model() <= 0))
        // the function can be evaluated on any (valid) dataset,
        && (forall<x: Vec<T>> inv(x) ==> t.function.pre()[x])
        // and returns its saturating sum
        && (forall<x: Vec<T>, r> t.function.post()[x][r] ==>
            exists<s: T> r == Ok(s) && s.deep_model() == sat_sum(x@))
    }
}

/// The contract of `make_bounded_int_monotonic_sum(bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn int_monotonic_sum_contract<T: Integer>(t: IntSum<T>, bounds: (T, T)) -> bool {
    pearlite! {
        t.input_domain.size == None
        && int_monotonic_sum_common(t, bounds)
        // the stability map returns at least d_in * max(|lower|, upper)
        && (forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
            exists<mag: T> mag.real() >= real_abs(bounds.0.real()) && mag.real() >= bounds.1.real()
                && o.real() >= Real::from_int(d@) * mag.real())
    }
}

/// The contract of `make_sized_bounded_int_monotonic_sum(size, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn sized_int_monotonic_sum_contract<T: Integer>(
    t: IntSum<T>,
    size: usize,
    bounds: (T, T),
) -> bool {
    pearlite! {
        t.input_domain.size == Some(size)
        && int_monotonic_sum_common(t, bounds)
        // the stability map returns at least (d_in / 2) * (upper - lower)
        && (forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
            o.real() >= Real::from_int(d@ / 2) * (bounds.1.real() - bounds.0.real()))
    }
}

/// `x` lies within `bounds`.
#[logic(open)]
pub fn in_bounds<T: Integer>(x: Vec<T>, bounds: (T, T)) -> bool {
    pearlite! {
        forall<i> 0 <= i && i < x@.len() ==>
            bounds.0.deep_model() <= x@[i].deep_model() && x@[i].deep_model() <= bounds.1.deep_model()
    }
}

/// The output of a monotonic sum is the clamped exact sum, and its real value is the clamped
/// real sum.
#[logic(prophetic)]
#[requires(int_monotonic_sum_common(t, bounds))]
#[requires(in_bounds(x, bounds))]
#[requires(t.function.post()[x][Ok(s)])]
#[ensures(s.deep_model() == clamp::<T>(isum(x@)))]
#[ensures(s.real() == Real::from_int(clamp::<T>(isum(x@))))]
#[ensures(sum(reals(x@)) == Real::from_int(isum(x@)))]
pub fn monotonic_sum_output<T: Integer>(t: IntSum<T>, bounds: (T, T), x: Vec<T>, s: T) {
    pearlite! {
        monotone_sat_sum(x@);
        integer_real(s);
        isum_real(x@)
    }
}

/// Clamping cannot increase the distance between two sums.
#[logic]
#[requires(real_abs(Real::from_int(p) - Real::from_int(q)) <= bound)]
#[ensures(real_abs(Real::from_int(clamp::<T>(p)) - Real::from_int(clamp::<T>(q))) <= bound)]
pub fn clamped_distance<T: Integer>(p: Int, q: Int, bound: Real) {
    pearlite! {
        clamp_lipschitz::<T>(p, q);
        proof_assert!(Real::from_int(clamp::<T>(p)) - Real::from_int(clamp::<T>(q)) == Real::from_int(clamp::<T>(p) - clamp::<T>(q)));
        proof_assert!(Real::from_int(p) - Real::from_int(q) == Real::from_int(p - q))
    }
}

/// Stability of `make_bounded_int_monotonic_sum`.
#[logic(prophetic)]
#[requires(int_monotonic_sum_contract(t, bounds))]
#[requires(in_bounds(x, bounds) && in_bounds(y, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(real_abs(sx.real() - sy.real()) <= o.real())]
pub fn int_monotonic_sum_is_stable<T: Integer>(
    t: IntSum<T>,
    bounds: (T, T),
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    sx: T,
    sy: T,
    o: T,
) {
    pearlite! {
        let (lo, hi) = bounds;
        monotonic_sum_output(t, bounds, x, sx);
        monotonic_sum_output(t, bounds, y, sy);
        let mag = such_that(|m: T| m.real() >= real_abs(lo.real()) && m.real() >= hi.real()
            && o.real() >= Real::from_int(d@) * m.real());
        real_bounds(x@, lo, hi, x@.len());
        real_bounds(y@, lo, hi, y@.len());
        unsized_sum_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real(), mag.real());
        clamped_distance::<T>(isum(x@), isum(y@), o.real())
    }
}

/// Stability of `make_sized_bounded_int_monotonic_sum`.
#[logic(prophetic)]
#[requires(sized_int_monotonic_sum_contract(t, size, bounds))]
#[requires(x@.len() == size@ && in_bounds(x, bounds) && y@.len() == size@ && in_bounds(y, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(real_abs(sx.real() - sy.real()) <= o.real())]
pub fn sized_int_monotonic_sum_is_stable<T: Integer>(
    t: IntSum<T>,
    size: usize,
    bounds: (T, T),
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    sx: T,
    sy: T,
    o: T,
) {
    pearlite! {
        let (lo, hi) = bounds;
        monotonic_sum_output(t, bounds, x, sx);
        monotonic_sum_output(t, bounds, y, sy);
        real_bounds(x@, lo, hi, x@.len());
        real_bounds(y@, lo, hi, y@.len());
        sized_sum_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real());
        clamped_distance::<T>(isum(x@), isum(y@), o.real())
    }
}
