//! Verification of `make_bounded_int_ordered_sum` and `make_sized_bounded_int_ordered_sum`.
//!
//! The function is the saturating sum, from left to right, with elements of either sign.
//! It is stable under the insert-delete distance (`verification::ordered`): deleting an element
//! moves a saturating sum by at most the element's magnitude, and keeping an element in both
//! datasets does not increase the difference between their saturating sums.
use creusot_std::{
    logic::{real::Real, such_that},
    prelude::*,
};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{AbsoluteDistance, InsertDeleteDistance, IntDistance},
    traits::Integer,
    verification::{
        integer::{integer_real, sat_sum},
        ordered::{bounded, id_close, sized_sat_sum_sensitivity, unsized_sat_sum_sensitivity},
        real_abs,
    },
};

pub type OrderedIntSum<T> = Transformation<
    VectorDomain<AtomDomain<T>>,
    InsertDeleteDistance,
    AtomDomain<T>,
    AbsoluteDistance<T>,
>;

/// The parts of the contracts shared by both constructors.
#[logic(open, prophetic, inline)]
pub fn int_ordered_sum_common<T: Integer>(t: OrderedIntSum<T>, bounds: (T, T)) -> bool {
    pearlite! {
        t.input_domain.element_domain.closed_bounds() == Some(bounds)
        && bounds.0.real() <= bounds.1.real()
        && (forall<x: Vec<T>> inv(x) ==> t.function.pre()[x])
        && (forall<x: Vec<T>, r> t.function.post()[x][r] ==>
            exists<s: T> r == Ok(s) && s.deep_model() == sat_sum(x@))
    }
}

/// The contract of `make_bounded_int_ordered_sum(bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn int_ordered_sum_contract<T: Integer>(t: OrderedIntSum<T>, bounds: (T, T)) -> bool {
    pearlite! {
        t.input_domain.size == None
        && int_ordered_sum_common(t, bounds)
        && (forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
            exists<mag: T> mag.real() >= real_abs(bounds.0.real()) && mag.real() >= bounds.1.real()
                && o.real() >= Real::from_int(d@) * mag.real())
    }
}

/// The contract of `make_sized_bounded_int_ordered_sum(size, bounds)` on success.
#[logic(open, prophetic, inline)]
pub fn sized_int_ordered_sum_contract<T: Integer>(
    t: OrderedIntSum<T>,
    size: usize,
    bounds: (T, T),
) -> bool {
    pearlite! {
        t.input_domain.size == Some(size)
        && int_ordered_sum_common(t, bounds)
        && (forall<d: IntDistance, o: T> t.stability_map.post()[d][Ok(o)] ==>
            o.real() >= Real::from_int(d@ / 2) * (bounds.1.real() - bounds.0.real()))
    }
}

/// Stability of `make_bounded_int_ordered_sum`.
#[logic(prophetic)]
#[requires(int_ordered_sum_contract(t, bounds))]
#[requires(bounded(x@, bounds.0.deep_model(), bounds.1.deep_model()))]
#[requires(bounded(y@, bounds.0.deep_model(), bounds.1.deep_model()))]
#[requires(id_close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(real_abs(sx.real() - sy.real()) <= o.real())]
pub fn int_ordered_sum_is_stable<T: Integer>(
    t: OrderedIntSum<T>,
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
        integer_real(lo);
        integer_real(hi);
        integer_real(sx);
        integer_real(sy);
        integer_real(o);
        let mag = such_that(|m: T| m.real() >= real_abs(lo.real()) && m.real() >= hi.real()
            && o.real() >= Real::from_int(d@) * m.real());
        integer_real(mag);
        unsized_sat_sum_sensitivity(x@, y@, d@, lo.deep_model(), hi.deep_model(), mag.deep_model());
        proof_assert!(Real::from_int(d@) * Real::from_int(mag.deep_model()) == Real::from_int(d@ * mag.deep_model()));
        proof_assert!(sx.real() - sy.real() == Real::from_int(sat_sum(x@) - sat_sum(y@)))
    }
}

/// Stability of `make_sized_bounded_int_ordered_sum`.
#[logic(prophetic)]
#[requires(sized_int_ordered_sum_contract(t, size, bounds))]
#[requires(x@.len() == size@ && bounded(x@, bounds.0.deep_model(), bounds.1.deep_model()))]
#[requires(y@.len() == size@ && bounded(y@, bounds.0.deep_model(), bounds.1.deep_model()))]
#[requires(id_close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(real_abs(sx.real() - sy.real()) <= o.real())]
pub fn sized_int_ordered_sum_is_stable<T: Integer>(
    t: OrderedIntSum<T>,
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
        integer_real(lo);
        integer_real(hi);
        integer_real(sx);
        integer_real(sy);
        sized_sat_sum_sensitivity(x@, y@, d@, lo.deep_model(), hi.deep_model());
        proof_assert!(Real::from_int(d@ / 2) * (hi.real() - lo.real())
            == Real::from_int((d@ / 2) * (hi.deep_model() - lo.deep_model())));
        proof_assert!(sx.real() - sy.real() == Real::from_int(sat_sum(x@) - sat_sum(y@)))
    }
}
