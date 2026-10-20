//! Verification of `make_bounded_int_split_sum` and `make_sized_bounded_int_split_sum`.
//!
//! The function sums negative and positive elements separately with saturating arithmetic, then
//! adds the two. Each partial sum only moves in one direction, so it is the clamped exact sum of
//! the negative (resp. positive) parts, and the output moves by at most the total change in those
//! exact sums (`split_distance`), which is bounded by `unsized_split_sensitivity` and
//! `sized_split_sensitivity`.
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
        dataset::{
            fsum, neg_part, pos_part, sized_split_sensitivity, sym_close, unsized_split_sensitivity,
        },
        integer::{
            clamp, clamp_lipschitz, integer_real, isum_neg, isum_parts_real, isum_pos, real_bounds,
            reals,
        },
        real_abs,
    },
};

use super::SplitSatSum;

pub type IntSum<T> = Transformation<
    VectorDomain<AtomDomain<T>>,
    SymmetricDistance,
    AtomDomain<T>,
    AbsoluteDistance<T>,
>;

/// The output of the split sum of `s`.
#[logic(open)]
pub fn split_sum_model<T: Integer>(s: Seq<T>) -> Int {
    pearlite! { clamp::<T>(clamp::<T>(isum_neg(s)) + clamp::<T>(isum_pos(s))) }
}

/// The parts of the contracts shared by both constructors.
#[logic(open, prophetic, inline)]
pub fn int_split_sum_common<T: Integer>(t: IntSum<T>, bounds: (T, T)) -> bool {
    pearlite! {
        t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        && (forall<x: Vec<T>> inv(x) ==> t.function.pre()[x])
        && (forall<x: Vec<T>, r> t.function.post()[x][r] ==>
            exists<s: T> r == Ok(s) && s.deep_model() == split_sum_model(x@))
    }
}

/// The contract of `make_bounded_int_split_sum(bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn int_split_sum_contract<T: Integer + SplitSatSum>(t: IntSum<T>, bounds: (T, T)) -> bool {
    pearlite! {
        t.input_domain.size == None
        && int_split_sum_common(t, bounds)
        && (forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
            exists<mag: T> mag.real() >= real_abs(bounds.0.real()) && mag.real() >= bounds.1.real()
                && o.real() >= Real::from_int(d@) * mag.real())
    }
}

/// The contract of `make_sized_bounded_int_split_sum(size, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn sized_int_split_sum_contract<T: Integer + SplitSatSum>(
    t: IntSum<T>,
    size: usize,
    bounds: (T, T),
) -> bool {
    pearlite! {
        t.input_domain.size == Some(size)
        && int_split_sum_common(t, bounds)
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

/// The output of the split sum moves by at most the total change in the sums of the parts.
#[logic]
#[requires(real_abs(Real::from_int(n1) - Real::from_int(n2)) + real_abs(Real::from_int(p1) - Real::from_int(p2)) <= bound)]
#[ensures(real_abs(Real::from_int(clamp::<T>(clamp::<T>(n1) + clamp::<T>(p1)))
    - Real::from_int(clamp::<T>(clamp::<T>(n2) + clamp::<T>(p2)))) <= bound)]
pub fn split_distance<T: Integer>(n1: Int, p1: Int, n2: Int, p2: Int, bound: Real) {
    pearlite! {
        clamp_lipschitz::<T>(n1, n2);
        clamp_lipschitz::<T>(p1, p2);
        let a = clamp::<T>(n1) + clamp::<T>(p1);
        let b = clamp::<T>(n2) + clamp::<T>(p2);
        clamp_lipschitz::<T>(a, b);
        proof_assert!(Real::from_int(clamp::<T>(a)) - Real::from_int(clamp::<T>(b)) == Real::from_int(clamp::<T>(a) - clamp::<T>(b)));
        proof_assert!(Real::from_int(n1) - Real::from_int(n2) == Real::from_int(n1 - n2));
        proof_assert!(Real::from_int(p1) - Real::from_int(p2) == Real::from_int(p1 - p2))
    }
}

/// The real value of the output, and the real sums of the parts of the input.
#[logic(prophetic)]
#[requires(int_split_sum_common(t, bounds))]
#[requires(t.function.post()[x][Ok(s)])]
#[ensures(s.real() == Real::from_int(split_sum_model(x@)))]
#[ensures(Real::from_int(isum_neg(x@)) == fsum(reals(x@), |v| neg_part(v)))]
#[ensures(Real::from_int(isum_pos(x@)) == fsum(reals(x@), |v| pos_part(v)))]
pub fn split_sum_output<T: Integer>(t: IntSum<T>, bounds: (T, T), x: Vec<T>, s: T) {
    pearlite! {
        integer_real(s);
        isum_parts_real(x@)
    }
}

/// Stability of `make_bounded_int_split_sum`.
#[logic(prophetic)]
#[requires(int_split_sum_contract(t, bounds))]
#[requires(in_bounds(x, bounds) && in_bounds(y, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(real_abs(sx.real() - sy.real()) <= o.real())]
pub fn int_split_sum_is_stable<T: Integer + SplitSatSum>(
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
        split_sum_output(t, bounds, x, sx);
        split_sum_output(t, bounds, y, sy);
        let mag = such_that(|m: T| m.real() >= real_abs(lo.real()) && m.real() >= hi.real()
            && o.real() >= Real::from_int(d@) * m.real());
        real_bounds(x@, lo, hi, x@.len());
        real_bounds(y@, lo, hi, y@.len());
        unsized_split_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real(), mag.real());
        split_distance::<T>(isum_neg(x@), isum_pos(x@), isum_neg(y@), isum_pos(y@), o.real())
    }
}

/// Stability of `make_sized_bounded_int_split_sum`.
#[logic(prophetic)]
#[requires(sized_int_split_sum_contract(t, size, bounds))]
#[requires(x@.len() == size@ && in_bounds(x, bounds) && y@.len() == size@ && in_bounds(y, bounds))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(real_abs(sx.real() - sy.real()) <= o.real())]
pub fn sized_int_split_sum_is_stable<T: Integer + SplitSatSum>(
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
        split_sum_output(t, bounds, x, sx);
        split_sum_output(t, bounds, y, sy);
        real_bounds(x@, lo, hi, x@.len());
        real_bounds(y@, lo, hi, y@.len());
        sized_split_sensitivity(reals(x@), reals(y@), d@, lo.real(), hi.real());
        split_distance::<T>(isum_neg(x@), isum_pos(x@), isum_neg(y@), isum_pos(y@), o.real())
    }
}
