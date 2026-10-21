//! Verification of `make_sized_bounded_int_checked_sum`.
//!
//! The constructor's contract (`sized_int_checked_sum_contract`) is checked by Creusot against
//! its implementation. The stability theorem (`sized_int_checked_sum_is_stable`) then shows that
//! any transformation satisfying the contract is stable: on any two datasets in the input domain
//! within symmetric distance `d_in`, the function is defined, and the sums differ by at most the
//! value of the stability map at `d_in`.
use creusot_std::{
    logic::{real::Real, such_that},
    prelude::*,
};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{AbsoluteDistance, IntDistance, SymmetricDistance},
    traits::Integer,
    verification::{
        dataset::{sized_sum_sensitivity, sum, sym_close},
        integer::{
            bounded_sums_fit, integer_real, isum, isum_real, overflow_witness, prefix_sums_fit,
            real_bounds, reals,
        },
        real_abs,
    },
};

pub type SizedIntSum<T> = Transformation<
    VectorDomain<AtomDomain<T>>,
    SymmetricDistance,
    AtomDomain<T>,
    AbsoluteDistance<T>,
>;

/// The contract of `make_sized_bounded_int_checked_sum(size, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn sized_int_checked_sum_contract<T: Integer>(
    t: SizedIntSum<T>,
    size: usize,
    bounds: (T, T),
) -> bool {
    pearlite! {
        // the input domain consists of vectors of `size` elements within `bounds`
        t.input_domain.size == Some(size)
        && t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        // a representable value bounds `size * max(|lower|, upper)`
        && (exists<mag: T, bound: T>
            mag.real() >= real_abs(bounds.0.real()) && mag.real() >= bounds.1.real()
            && bound.real() >= mag.real() * Real::from_int(size@))
        // the function can be evaluated on any (valid) dataset whose sum cannot overflow,
        && (forall<x: Vec<T>> inv(x) && prefix_sums_fit(x@) ==> t.function.pre()[x])
        // and then returns its exact sum
        && (forall<x: Vec<T>, r> prefix_sums_fit(x@) && t.function.post()[x][r] ==>
            exists<s: T> r == Ok(s) && s.deep_model() == isum(x@))
        // the stability map returns at least (d_in / 2) * (upper - lower)
        && (forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
            o.real() >= Real::from_int(d@ / 2) * (bounds.1.real() - bounds.0.real()))
    }
}

/// `x` is in the input domain: `size` elements within `bounds`.
#[logic(open)]
pub fn in_sized_bounded_domain<T: Integer>(x: Vec<T>, size: usize, bounds: (T, T)) -> bool {
    pearlite! {
        x@.len() == size@
        && forall<i> 0 <= i && i < x@.len() ==>
            bounds.0.deep_model() <= x@[i].deep_model() && x@[i].deep_model() <= bounds.1.deep_model()
    }
}

/// On any dataset in the input domain, the function of `make_sized_bounded_int_checked_sum`
/// can be evaluated, does not fail, and returns the exact sum.
#[logic(prophetic)]
#[requires(sized_int_checked_sum_contract(t, size, bounds))]
#[requires(inv(x) && in_sized_bounded_domain(x, size, bounds))]
#[ensures(result && t.function.pre()[x]
    && forall<r> t.function.post()[x][r] ==> exists<s: T> r == Ok(s) && s.real() == sum(reals(x@)))]
pub fn sized_int_checked_sum_is_defined<T: Integer>(
    t: SizedIntSum<T>,
    size: usize,
    bounds: (T, T),
    x: Vec<T>,
) -> bool {
    pearlite! {
        let (lo, hi) = bounds;
        // the sum cannot overflow
        let (mag, bound) = such_that(|w: (T, T)|
            w.0.real() >= real_abs(lo.real()) && w.0.real() >= hi.real()
            && w.1.real() >= w.0.real() * Real::from_int(size@));
        overflow_witness(lo, hi, mag, bound, size@);
        bounded_sums_fit(x@, lo, hi, bound);
        // the real sum of the dataset is its integer sum
        isum_real(x@);
        proof_assert!(forall<s: T> s.deep_model() == isum(x@) ==> { integer_real(s); s.real() == sum(reals(x@)) });
        true
    }
}

/// Stability of `make_sized_bounded_int_checked_sum`: on any two datasets in the input domain
/// within symmetric distance `d`, the outputs differ by at most the stability map at `d`.
#[logic(prophetic)]
#[requires(sized_int_checked_sum_contract(t, size, bounds))]
#[requires(inv(x) && in_sized_bounded_domain(x, size, bounds))]
#[requires(inv(y) && in_sized_bounded_domain(y, size, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn sized_int_checked_sum_is_stable<T: Integer>(
    t: SizedIntSum<T>,
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
        sized_int_checked_sum_is_defined(t, size, bounds, x);
        sized_int_checked_sum_is_defined(t, size, bounds, y);
        real_bounds(x@, lo, hi, x@.len());
        real_bounds(y@, lo, hi, y@.len());
        sized_sum_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real());
        true
    }
}
