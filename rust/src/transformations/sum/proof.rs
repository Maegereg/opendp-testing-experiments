//! Verification of `make_sum`: on success, it returns a transformation that is stable on its input
//! domain, for every integer and float type and both input metrics.
//!
//! Each branch of the dispatcher returns one of the verified sums, possibly after
//! `make_unordered` (insert-delete to symmetric distance) or `make_ordered_random` (a shuffle,
//! symmetric to insert-delete distance). The lemmas here lift each sum's contract to the
//! stability property of `make_sum`, and compose the contracts of `make_unordered` and
//! `make_ordered_random` with them.
//!
//! When `make_sum` shuffles, the output is random, so stability is stated as a matching: every
//! ordering of `x` is matched with an ordering of `y`, and the sums of matched orderings differ by
//! at most the map (`float_sym_shuffled_stable`). That a uniform shuffle of `x` couples with a
//! uniform shuffle of `y` this way is cited (`verification::cast_metric::shuffle_match`).
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};

use super::DEFAULT_SIZE_LIMIT;
use crate::{
    combinators::is_chain_tt,
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{AbsoluteDistance, InsertDeleteDistance, IntDistance, SymmetricDistance},
    traits::{
        Float, Integer,
        samplers::{Shuffle, vec_reorders},
    },
    transformations::{
        Pairwise, SaturatingSum, Sequential, SplitSatSum, SumRelaxation,
        float_checked_sum_contract, float_checked_sum_is_stable, float_ordered_sum_contract,
        float_ordered_sum_is_stable, int_monotonic_sum_contract, int_monotonic_sum_is_stable,
        int_ordered_sum_contract, int_ordered_sum_is_stable, int_split_sum_contract,
        int_split_sum_is_stable, ordered_random_contract, seq_saturating_sum_stable,
        sized_float_checked_sum_contract, sized_float_checked_sum_is_stable,
        sized_float_ordered_sum_contract, sized_float_ordered_sum_is_stable,
        sized_int_checked_sum_contract, sized_int_checked_sum_is_defined,
        sized_int_checked_sum_is_stable, sized_int_monotonic_sum_contract,
        sized_int_monotonic_sum_is_stable, sized_int_ordered_sum_contract,
        sized_int_ordered_sum_is_stable, sized_int_split_sum_contract,
        sized_int_split_sum_is_stable, sized_seq_saturating_sum_stable, unordered_contract,
    },
    verification::{
        cast_metric::{id_close_sym_close, int_id_close_sym_close, number_clone, shuffle_match},
        clamped,
        dataset::{decompose, sym_close},
        float::{float_in_bounds, mag, reals},
        ordered, real_abs,
    },
};

/// A sum transformation over vectors of `T` under the input metric `MI`.
pub type SumT<T, MI> =
    Transformation<VectorDomain<AtomDomain<T>>, MI, AtomDomain<T>, AbsoluteDistance<T>>;

/// A transformation that changes the dataset metric (`make_unordered`, `make_ordered_random`).
pub type CastT<T, MI, MO> =
    Transformation<VectorDomain<AtomDomain<T>>, MI, VectorDomain<AtomDomain<T>>, MO>;

/// Symmetric neighbours are also neighbours at any larger distance.
#[logic]
#[requires(sym_close(x, y, d) && d <= m)]
#[ensures(sym_close(x, y, m))]
pub fn sym_close_mono(x: Seq<Real>, y: Seq<Real>, d: Int, m: Int) {
    pearlite! { let _ = decompose(x, y, d); }
}

// ---------------------------------------------------------------------------------------------
// Integers

/// `x` is in `make_sum`'s input domain: its elements lie within `bounds`, and it has `size`
/// elements if `size` is known.
#[logic(open)]
pub fn int_in_domain<T: Integer>(x: Seq<T>, bounds: (T, T), size: Option<usize>) -> bool {
    pearlite! {
        ordered::bounded(x, bounds.0.deep_model(), bounds.1.deep_model())
        && match size { Some(n) => x.len() == n@, None => true }
    }
}

/// The function of `t` can be evaluated on every dataset in the input domain.
#[logic(open, prophetic)]
pub fn int_defined<T: Integer, MI: crate::core::Metric>(
    t: SumT<T, MI>,
    bounds: (T, T),
    size: Option<usize>,
) -> bool {
    pearlite! { forall<x: Vec<T>> inv(x) && int_in_domain(x@, bounds, size) ==> t.function.pre()[x] }
}

/// `t` is stable under the symmetric distance: on datasets in the input domain within distance
/// `d`, the outputs differ by at most the map at `d`.
#[logic(open, prophetic)]
pub fn int_sym_stable<T: Integer>(
    t: SumT<T, SymmetricDistance>,
    bounds: (T, T),
    size: Option<usize>,
) -> bool {
    pearlite! {
        int_defined(t, bounds, size)
        && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
            inv(x) && inv(y) && int_in_domain(x@, bounds, size) && int_in_domain(y@, bounds, size)
            && sym_close(reals(x@), reals(y@), d@)
            && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
            && t.stability_map.post()[d][Ok(o)]
            ==> real_abs(sx.real() - sy.real()) <= o.real()
    }
}

/// `t` is stable under the insert-delete distance.
#[logic(open, prophetic)]
pub fn int_id_stable<T: Integer>(
    t: SumT<T, InsertDeleteDistance>,
    bounds: (T, T),
    size: Option<usize>,
) -> bool {
    pearlite! {
        int_defined(t, bounds, size)
        && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
            inv(x) && inv(y) && int_in_domain(x@, bounds, size) && int_in_domain(y@, bounds, size)
            && ordered::id_close(x@, y@, d@)
            && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
            && t.stability_map.post()[d][Ok(o)]
            ==> real_abs(sx.real() - sy.real()) <= o.real()
    }
}

/// `make_sum`'s property for integers under the symmetric distance.
#[logic(open, prophetic)]
pub fn int_sym_sum_is_stable<T: Integer>(
    t: SumT<T, SymmetricDistance>,
    input_domain: VectorDomain<AtomDomain<T>>,
) -> bool {
    pearlite! {
        match input_domain.element_domain.closed_bounds() {
            Some(bounds) => int_sym_stable(t, bounds, input_domain.size),
            None => false,
        }
    }
}

/// `make_sum`'s property for integers under the insert-delete distance.
#[logic(open, prophetic)]
pub fn int_id_sum_is_stable<T: Integer>(
    t: SumT<T, InsertDeleteDistance>,
    input_domain: VectorDomain<AtomDomain<T>>,
) -> bool {
    pearlite! {
        match input_domain.element_domain.closed_bounds() {
            Some(bounds) => int_id_stable(t, bounds, input_domain.size),
            None => false,
        }
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    sized_int_checked_sum_contract(t, size, bounds) ==> int_sym_stable(t, bounds, Some(size)))]
pub fn sized_int_checked_lift<T: Integer>(size: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> sized_int_checked_sum_contract(t, size, bounds) ==>
            (forall<x: Vec<T>> inv(x) && int_in_domain(x@, bounds, Some(size)) ==>
                sized_int_checked_sum_is_defined(t, size, bounds, x))
            && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, Some(size)) && int_in_domain(y@, bounds, Some(size))
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> sized_int_checked_sum_is_stable(t, size, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    int_monotonic_sum_contract(t, bounds) ==> int_sym_stable(t, bounds, None))]
pub fn int_monotonic_lift<T: Integer>(bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> int_monotonic_sum_contract(t, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, None) && int_in_domain(y@, bounds, None)
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> int_monotonic_sum_is_stable(t, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    sized_int_monotonic_sum_contract(t, size, bounds) ==> int_sym_stable(t, bounds, Some(size)))]
pub fn sized_int_monotonic_lift<T: Integer>(size: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> sized_int_monotonic_sum_contract(t, size, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, Some(size)) && int_in_domain(y@, bounds, Some(size))
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> sized_int_monotonic_sum_is_stable(t, size, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    int_split_sum_contract(t, bounds) ==> int_sym_stable(t, bounds, None))]
pub fn int_split_lift<T: Integer + SplitSatSum>(bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> int_split_sum_contract(t, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, None) && int_in_domain(y@, bounds, None)
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> int_split_sum_is_stable(t, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    sized_int_split_sum_contract(t, size, bounds) ==> int_sym_stable(t, bounds, Some(size)))]
pub fn sized_int_split_lift<T: Integer + SplitSatSum>(size: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> sized_int_split_sum_contract(t, size, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, Some(size)) && int_in_domain(y@, bounds, Some(size))
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> sized_int_split_sum_is_stable(t, size, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, InsertDeleteDistance>>
    int_ordered_sum_contract(t, bounds) ==> int_id_stable(t, bounds, None))]
pub fn int_ordered_lift<T: Integer>(bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, InsertDeleteDistance>> int_ordered_sum_contract(t, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, None) && int_in_domain(y@, bounds, None)
                && ordered::id_close(x@, y@, d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> int_ordered_sum_is_stable(t, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, InsertDeleteDistance>>
    sized_int_ordered_sum_contract(t, size, bounds) ==> int_id_stable(t, bounds, Some(size)))]
pub fn sized_int_ordered_lift<T: Integer>(size: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, InsertDeleteDistance>> sized_int_ordered_sum_contract(t, size, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, Some(size)) && int_in_domain(y@, bounds, Some(size))
                && ordered::id_close(x@, y@, d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> sized_int_ordered_sum_is_stable(t, size, bounds, x, y, d, sx, sy, o));
        true
    }
}

/// `make_unordered` returns a copy of its input.
#[logic(prophetic)]
#[requires(unordered_contract(t0))]
#[requires(t0.function.post()[x][Ok(x2)])]
#[ensures(result && inv(x2) && x2@ == x@)]
pub fn unordered_copy<T: crate::traits::Number>(
    t0: CastT<T, InsertDeleteDistance, SymmetricDistance>,
    x: Vec<T>,
    x2: Vec<T>,
) -> bool {
    pearlite! {
        number_clone::<T>();
        proof_assert!(x2@.ext_eq(x@));
        true
    }
}

/// One instance of `int_unordered_lift`.
#[logic(prophetic)]
#[requires(unordered_contract(t0) && int_sym_stable(t1, bounds, size) && is_chain_tt(t, t1, t0))]
#[requires(inv(x) && inv(y) && int_in_domain(x@, bounds, size) && int_in_domain(y@, bounds, size))]
#[requires(ordered::id_close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn int_unordered_step<T: Integer>(
    t0: CastT<T, InsertDeleteDistance, SymmetricDistance>,
    t1: SumT<T, SymmetricDistance>,
    t: SumT<T, InsertDeleteDistance>,
    bounds: (T, T),
    size: Option<usize>,
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    sx: T,
    sy: T,
    o: T,
) -> bool {
    pearlite! {
        let x2 = such_that(|x2: Vec<T>| t0.function.post()[x][Ok(x2)] && t1.function.post()[x2][Ok(sx)]);
        let y2 = such_that(|y2: Vec<T>| t0.function.post()[y][Ok(y2)] && t1.function.post()[y2][Ok(sy)]);
        let m = such_that(|m: IntDistance| t0.stability_map.post()[d][Ok(m)] && t1.stability_map.post()[m][Ok(o)]);
        proof_assert!(unordered_copy(t0, x, x2) && unordered_copy(t0, y, y2));
        int_id_close_sym_close(x@, y@, d@);
        sym_close_mono(reals(x@), reals(y@), d@, m@);
        proof_assert!(sym_close(reals(x2@), reals(y2@), m@));
        proof_assert!(inv(x2) && inv(y2) && int_in_domain(x2@, bounds, size) && int_in_domain(y2@, bounds, size));
        proof_assert!(t1.function.post()[x2][Ok(sx)] && t1.function.post()[y2][Ok(sy)]
            && t1.stability_map.post()[m][Ok(o)]);
        true
    }
}

/// `make_unordered` followed by a sum that is stable under the symmetric distance is stable under
/// the insert-delete distance.
#[logic(prophetic)]
#[ensures(result && forall<t0: CastT<T, InsertDeleteDistance, SymmetricDistance>, t1: SumT<T, SymmetricDistance>, t: SumT<T, InsertDeleteDistance>>
    unordered_contract(t0) && int_sym_stable(t1, bounds, size) && is_chain_tt(t, t1, t0)
    ==> int_id_stable(t, bounds, size))]
pub fn int_unordered_lift<T: Integer>(bounds: (T, T), size: Option<usize>) -> bool {
    pearlite! {
        proof_assert!(forall<t0: CastT<T, InsertDeleteDistance, SymmetricDistance>, t1: SumT<T, SymmetricDistance>, t: SumT<T, InsertDeleteDistance>>
            unordered_contract(t0) && int_sym_stable(t1, bounds, size) && is_chain_tt(t, t1, t0) ==>
            (forall<x: Vec<T>> inv(x) && int_in_domain(x@, bounds, size) ==>
                (forall<x2: Vec<T>> t0.function.post()[x][Ok(x2)] ==> unordered_copy(t0, x, x2))
                && t.function.pre()[x])
            && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                inv(x) && inv(y) && int_in_domain(x@, bounds, size) && int_in_domain(y@, bounds, size)
                && ordered::id_close(x@, y@, d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> int_unordered_step(t0, t1, t, bounds, size, x, y, d, sx, sy, o));
        true
    }
}

// ---------------------------------------------------------------------------------------------
// Floats

/// `x` is in `make_sum`'s input domain: its elements are finite and lie within `bounds`, and it
/// has `size` elements if `size` is known. Otherwise, the theorems cover datasets of at most
/// `DEFAULT_SIZE_LIMIT` elements (larger ones are truncated, as for the sums themselves).
#[logic(open)]
pub fn float_in_domain<T: Float>(
    x: Seq<T>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
) -> bool {
    pearlite! {
        float_in_bounds(x, bounds)
        && match size { Some(n) => x.len() == n@, None => x.len() <= limit@ }
    }
}

/// The function of `t` can be evaluated on every dataset in the input domain.
#[logic(open, prophetic)]
pub fn float_defined<T: Float, MI: crate::core::Metric>(
    t: SumT<T, MI>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
) -> bool {
    pearlite! { forall<x: Vec<T>> inv(x) && float_in_domain(x@, bounds, size, limit) ==> t.function.pre()[x] }
}

/// `t` is stable under the symmetric distance.
#[logic(open, prophetic)]
pub fn float_sym_stable<T: Float>(
    t: SumT<T, SymmetricDistance>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
) -> bool {
    pearlite! {
        float_defined(t, bounds, size, limit)
        && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
            float_in_domain(x@, bounds, size, limit) && float_in_domain(y@, bounds, size, limit)
            && sym_close(reals(x@), reals(y@), d@)
            && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
            && t.stability_map.post()[d][Ok(o)]
            ==> real_abs(sx.real() - sy.real()) <= o.real()
    }
}

/// `t` is stable under the insert-delete distance.
#[logic(open, prophetic)]
pub fn float_id_stable<T: Float>(
    t: SumT<T, InsertDeleteDistance>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
) -> bool {
    pearlite! {
        float_defined(t, bounds, size, limit)
        && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
            float_in_domain(x@, bounds, size, limit) && float_in_domain(y@, bounds, size, limit)
            && clamped::id_close(reals(x@), reals(y@), d@)
            && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
            && t.stability_map.post()[d][Ok(o)]
            ==> real_abs(sx.real() - sy.real()) <= o.real()
    }
}

/// `t` shuffles, then takes the sequential saturating sum, and is stable under the symmetric
/// distance up to a matching of the shuffles: every ordering `px` of `x` is matched with an
/// ordering `py` of `y` whose sum is within the map of the sum of `px`.
#[logic(open, prophetic)]
pub fn float_sym_shuffled_stable<T: Float>(
    t: SumT<T, SymmetricDistance>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
) -> bool {
    pearlite! {
        float_defined(t, bounds, size, limit)
        // the output is the saturating sum of an ordering of the input,
        && (forall<x: Vec<T>, s: T> #[trigger(t.function.post()[x][Ok(s)])] inv(x) && float_in_domain(x@, bounds, size, limit) && t.function.post()[x][Ok(s)] ==>
            exists<px: Seq<T>> px.permutation_of(x@) && s == Sequential::<T>::saturating_sum_logic(px))
        // and orderings of neighbours can be matched within the map
        && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, o: T, px: Seq<T>>
            #[trigger(t.stability_map.post()[d][Ok(o)], px.permutation_of(x@), sym_close(reals(x@), reals(y@), d@))]
            float_in_domain(x@, bounds, size, limit) && float_in_domain(y@, bounds, size, limit)
            && sym_close(reals(x@), reals(y@), d@)
            && t.stability_map.post()[d][Ok(o)]
            && px.permutation_of(x@)
            ==> exists<py: Seq<T>> py.permutation_of(y@)
                && real_abs(Sequential::<T>::saturating_sum_logic(px).real()
                    - Sequential::<T>::saturating_sum_logic(py).real()) <= o.real()
    }
}

/// `make_sum`'s property for floats under the symmetric distance.
#[logic(open(super), prophetic)]
pub fn float_sym_sum_is_stable<T: Float>(
    t: SumT<T, SymmetricDistance>,
    input_domain: VectorDomain<AtomDomain<T>>,
) -> bool {
    pearlite! {
        match input_domain.element_domain.closed_bounds() {
            Some(bounds) => float_sym_stable(t, bounds, input_domain.size, DEFAULT_SIZE_LIMIT)
                || float_sym_shuffled_stable(t, bounds, input_domain.size, DEFAULT_SIZE_LIMIT),
            None => false,
        }
    }
}

/// `make_sum`'s property for floats under the insert-delete distance.
#[logic(open(super), prophetic)]
pub fn float_id_sum_is_stable<T: Float>(
    t: SumT<T, InsertDeleteDistance>,
    input_domain: VectorDomain<AtomDomain<T>>,
) -> bool {
    pearlite! {
        match input_domain.element_domain.closed_bounds() {
            Some(bounds) => float_id_stable(t, bounds, input_domain.size, DEFAULT_SIZE_LIMIT),
            None => false,
        }
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    float_checked_sum_contract::<Pairwise<T>>(t, n, bounds) ==> float_sym_stable(t, bounds, None, n))]
pub fn float_checked_lift<T: Float>(n: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> float_checked_sum_contract::<Pairwise<T>>(t, n, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                float_in_domain(x@, bounds, None, n) && float_in_domain(y@, bounds, None, n)
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> float_checked_sum_is_stable::<Pairwise<T>>(t, n, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, SymmetricDistance>>
    sized_float_checked_sum_contract::<Pairwise<T>>(t, size, bounds) ==> float_sym_stable(t, bounds, Some(size), limit))]
pub fn sized_float_checked_lift<T: Float>(size: usize, bounds: (T, T), limit: usize) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, SymmetricDistance>> sized_float_checked_sum_contract::<Pairwise<T>>(t, size, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                float_in_domain(x@, bounds, Some(size), limit) && float_in_domain(y@, bounds, Some(size), limit)
                && sym_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> sized_float_checked_sum_is_stable::<Pairwise<T>>(t, size, bounds, x, y, d, sx, sy, o));
        true
    }
}

/// The contract of `make_bounded_float_ordered_sum::<Sequential<T>>`, as a predicate that is not
/// inlined (so that it can be matched in the dispatcher).
#[logic(open, prophetic)]
pub fn seq_ordered_contract<T: Float>(
    t: SumT<T, InsertDeleteDistance>,
    n: usize,
    bounds: (T, T),
) -> bool {
    pearlite! { float_ordered_sum_contract::<Sequential<T>>(t, n, bounds) }
}

/// The contract of `make_sized_bounded_float_ordered_sum::<Sequential<T>>`, as a predicate that is
/// not inlined.
#[logic(open, prophetic)]
pub fn sized_seq_ordered_contract<T: Float>(
    t: SumT<T, InsertDeleteDistance>,
    size: usize,
    bounds: (T, T),
) -> bool {
    pearlite! { sized_float_ordered_sum_contract::<Sequential<T>>(t, size, bounds) }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, InsertDeleteDistance>>
    seq_ordered_contract(t, n, bounds) ==> float_id_stable(t, bounds, None, n))]
pub fn float_ordered_lift<T: Float>(n: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, InsertDeleteDistance>> seq_ordered_contract(t, n, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                float_in_domain(x@, bounds, None, n) && float_in_domain(y@, bounds, None, n)
                && clamped::id_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> float_ordered_sum_is_stable(t, n, bounds, x, y, d, sx, sy, o));
        true
    }
}

#[logic(prophetic)]
#[ensures(result && forall<t: SumT<T, InsertDeleteDistance>>
    sized_float_ordered_sum_contract::<Sequential<T>>(t, size, bounds) ==> float_id_stable(t, bounds, Some(size), limit))]
pub fn sized_float_ordered_lift<T: Float>(size: usize, bounds: (T, T), limit: usize) -> bool {
    pearlite! {
        proof_assert!(forall<t: SumT<T, InsertDeleteDistance>> sized_float_ordered_sum_contract::<Sequential<T>>(t, size, bounds) ==>
            forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                float_in_domain(x@, bounds, Some(size), limit) && float_in_domain(y@, bounds, Some(size), limit)
                && clamped::id_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> sized_float_ordered_sum_is_stable(t, size, bounds, x, y, d, sx, sy, o));
        true
    }
}

/// One instance of `float_unordered_lift`.
#[logic(prophetic)]
#[requires(unordered_contract(t0) && float_sym_stable(t1, bounds, size, limit) && is_chain_tt(t, t1, t0))]
#[requires(float_in_domain(x@, bounds, size, limit) && float_in_domain(y@, bounds, size, limit))]
#[requires(clamped::id_close(reals(x@), reals(y@), d@))]
#[requires(t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(result && real_abs(sx.real() - sy.real()) <= o.real())]
pub fn float_unordered_step<T: Float>(
    t0: CastT<T, InsertDeleteDistance, SymmetricDistance>,
    t1: SumT<T, SymmetricDistance>,
    t: SumT<T, InsertDeleteDistance>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    sx: T,
    sy: T,
    o: T,
) -> bool {
    pearlite! {
        let x2 = such_that(|x2: Vec<T>| t0.function.post()[x][Ok(x2)] && t1.function.post()[x2][Ok(sx)]);
        let y2 = such_that(|y2: Vec<T>| t0.function.post()[y][Ok(y2)] && t1.function.post()[y2][Ok(sy)]);
        let m = such_that(|m: IntDistance| t0.stability_map.post()[d][Ok(m)] && t1.stability_map.post()[m][Ok(o)]);
        proof_assert!(unordered_copy(t0, x, x2) && unordered_copy(t0, y, y2));
        id_close_sym_close(reals(x@), reals(y@), d@);
        sym_close_mono(reals(x@), reals(y@), d@, m@);
        proof_assert!(sym_close(reals(x2@), reals(y2@), m@));
        proof_assert!(float_in_domain(x2@, bounds, size, limit) && float_in_domain(y2@, bounds, size, limit));
        proof_assert!(t1.function.post()[x2][Ok(sx)] && t1.function.post()[y2][Ok(sy)]
            && t1.stability_map.post()[m][Ok(o)]);
        true
    }
}

/// `make_unordered` followed by a sum that is stable under the symmetric distance is stable under
/// the insert-delete distance.
#[logic(prophetic)]
#[ensures(result && forall<t0: CastT<T, InsertDeleteDistance, SymmetricDistance>, t1: SumT<T, SymmetricDistance>, t: SumT<T, InsertDeleteDistance>>
    unordered_contract(t0) && float_sym_stable(t1, bounds, size, limit) && is_chain_tt(t, t1, t0)
    ==> float_id_stable(t, bounds, size, limit))]
pub fn float_unordered_lift<T: Float>(bounds: (T, T), size: Option<usize>, limit: usize) -> bool {
    pearlite! {
        proof_assert!(forall<t0: CastT<T, InsertDeleteDistance, SymmetricDistance>, t1: SumT<T, SymmetricDistance>, t: SumT<T, InsertDeleteDistance>>
            unordered_contract(t0) && float_sym_stable(t1, bounds, size, limit) && is_chain_tt(t, t1, t0) ==>
            (forall<x: Vec<T>> inv(x) && float_in_domain(x@, bounds, size, limit) ==>
                (forall<x2: Vec<T>> t0.function.post()[x][Ok(x2)] ==> unordered_copy(t0, x, x2))
                && t.function.pre()[x])
            && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, sx: T, sy: T, o: T>
            #[trigger(t.function.post()[x][Ok(sx)], t.function.post()[y][Ok(sy)], t.stability_map.post()[d][Ok(o)])]
                float_in_domain(x@, bounds, size, limit) && float_in_domain(y@, bounds, size, limit)
                && clamped::id_close(reals(x@), reals(y@), d@)
                && t.function.post()[x][Ok(sx)] && t.function.post()[y][Ok(sy)]
                && t.stability_map.post()[d][Ok(o)]
                ==> float_unordered_step(t0, t1, t, bounds, size, limit, x, y, d, sx, sy, o));
        true
    }
}

/// `make_ordered_random` returns an ordering of its input.
#[logic(prophetic)]
#[requires(ordered_random_contract(t0))]
#[requires(t0.function.post()[x][Ok(x2)])]
#[ensures(result && inv(x2) && x2@.permutation_of(x@))]
pub fn shuffled_copy<T: Float>(
    t0: CastT<T, SymmetricDistance, InsertDeleteDistance>,
    x: Vec<T>,
    x2: Vec<T>,
) -> bool {
    pearlite! {
        let c = such_that(|c: Vec<T>| <Vec<T> as Clone>::clone.postcondition((&x,), c) && c.reorders(x2));
        number_clone::<T>();
        proof_assert!(c@.ext_eq(x@));
        vec_reorders(c, x2);
        true
    }
}

/// The sum of a shuffle that returns the sequential saturating sum of its input (of at most
/// `DEFAULT_SIZE_LIMIT` values) is the saturating sum of an ordering of the input.
#[logic(prophetic)]
#[requires(ordered_random_contract(t0) && is_chain_tt(t, t1, t0))]
#[requires(forall<x2: Vec<T>, r: T> float_in_domain(x2@, bounds, size, limit) && t1.function.post()[x2][Ok(r)] ==>
    r == Sequential::<T>::saturating_sum_logic(x2@))]
#[requires(inv(x) && float_in_domain(x@, bounds, size, limit) && t.function.post()[x][Ok(s)])]
#[ensures(result && exists<px: Seq<T>> px.permutation_of(x@) && s == Sequential::<T>::saturating_sum_logic(px))]
pub fn shuffled_output<T: Float>(
    t0: CastT<T, SymmetricDistance, InsertDeleteDistance>,
    t1: SumT<T, InsertDeleteDistance>,
    t: SumT<T, SymmetricDistance>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
    x: Vec<T>,
    s: T,
) -> bool {
    pearlite! {
        let x2 = such_that(|x2: Vec<T>| t0.function.post()[x][Ok(x2)] && t1.function.post()[x2][Ok(s)]);
        proof_assert!(shuffled_copy(t0, x, x2));
        shuffled_in_domain(x@, x2@, bounds, size, limit);
        proof_assert!(x2@.permutation_of(x@) && s == Sequential::<T>::saturating_sum_logic(x2@));
        true
    }
}

/// An ordering of a dataset in the input domain is in the input domain.
#[logic]
#[requires(px.permutation_of(x) && float_in_domain(x, bounds, size, limit))]
#[ensures(float_in_domain(px, bounds, size, limit))]
pub fn shuffled_in_domain<T: Float>(
    x: Seq<T>,
    px: Seq<T>,
    bounds: (T, T),
    size: Option<usize>,
    limit: usize,
) {
    pearlite! {
        proof_assert!(px.len() == x.len());
        proof_assert!(forall<i> 0 <= i && i < px.len() ==> exists<j> 0 <= j && j < x.len() && px[i] == x[j])
    }
}

/// One instance of the matching in `shuffled_float_ordered_lift`.
#[logic(prophetic)]
#[requires(ordered_random_contract(t0))]
#[requires(float_ordered_sum_contract::<Sequential<T>>(t1, n, bounds))]
#[requires(is_chain_tt(t, t1, t0))]
#[requires(float_in_domain(x@, bounds, None, n) && float_in_domain(y@, bounds, None, n))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[requires(px.permutation_of(x@))]
#[ensures(result.permutation_of(y@))]
#[ensures(real_abs(Sequential::<T>::saturating_sum_logic(px).real()
    - Sequential::<T>::saturating_sum_logic(result).real()) <= o.real())]
pub fn shuffled_match_step<T: Float>(
    t0: CastT<T, SymmetricDistance, InsertDeleteDistance>,
    t1: SumT<T, InsertDeleteDistance>,
    t: SumT<T, SymmetricDistance>,
    n: usize,
    bounds: (T, T),
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    o: T,
    px: Seq<T>,
) -> Seq<T> {
    pearlite! {
        let mg = mag(bounds.0.real(), bounds.1.real());
        let m = such_that(|m: IntDistance| t0.stability_map.post()[d][Ok(m)] && t1.stability_map.post()[m][Ok(o)]);
        let e = such_that(|e: Real|
            Sequential::<T>::error_bound(n@, Real::from_int(n@) * mg, e)
            && forall<d: IntDistance, o: T> t1.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@) * mg + e + e);
        let py = shuffle_match(x@, y@, d@, px);
        shuffled_in_domain(x@, px, bounds, None, n);
        shuffled_in_domain(y@, py, bounds, None, n);
        seq_saturating_sum_stable(n, bounds, e, px, py, d@);
        proof_assert!(mg >= Real::from_int(0));
        proof_assert!(Real::from_int(d@) * mg <= Real::from_int(m@) * mg);
        py
    }
}

/// `make_ordered_random` followed by the sequential saturating sum is stable under the symmetric
/// distance, up to the matching of shuffles.
#[logic(prophetic)]
#[ensures(result && forall<t0: CastT<T, SymmetricDistance, InsertDeleteDistance>, t1: SumT<T, InsertDeleteDistance>, t: SumT<T, SymmetricDistance>>
    ordered_random_contract(t0) && seq_ordered_contract(t1, n, bounds)
    && is_chain_tt(t, t1, t0)
    ==> float_sym_shuffled_stable(t, bounds, None, n))]
pub fn shuffled_float_ordered_lift<T: Float>(n: usize, bounds: (T, T)) -> bool {
    pearlite! {
        proof_assert!(forall<x2: Vec<T>> x2@.subsequence(0, x2@.len()) == x2@);
        proof_assert!(forall<t0: CastT<T, SymmetricDistance, InsertDeleteDistance>, t1: SumT<T, InsertDeleteDistance>, t: SumT<T, SymmetricDistance>>
            ordered_random_contract(t0) && seq_ordered_contract(t1, n, bounds)
            && is_chain_tt(t, t1, t0) ==>
            (forall<x: Vec<T>> inv(x) && float_in_domain(x@, bounds, None, n) ==> t.function.pre()[x])
            && (forall<x: Vec<T>, s: T> #[trigger(t.function.post()[x][Ok(s)])] inv(x) && float_in_domain(x@, bounds, None, n) && t.function.post()[x][Ok(s)] ==>
                shuffled_output(t0, t1, t, bounds, None, n, x, s))
            && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, o: T, px: Seq<T>>
            #[trigger(t.stability_map.post()[d][Ok(o)], px.permutation_of(x@), sym_close(reals(x@), reals(y@), d@))]
                float_in_domain(x@, bounds, None, n) && float_in_domain(y@, bounds, None, n)
                && sym_close(reals(x@), reals(y@), d@)
                && t.stability_map.post()[d][Ok(o)]
                && px.permutation_of(x@)
                ==> {
                    let py = shuffled_match_step(t0, t1, t, n, bounds, x, y, d, o, px);
                    py.permutation_of(y@)
                        && real_abs(Sequential::<T>::saturating_sum_logic(px).real()
                            - Sequential::<T>::saturating_sum_logic(py).real()) <= o.real()
                });
        true
    }
}

/// One instance of the matching in `sized_shuffled_float_ordered_lift`.
#[logic(prophetic)]
#[requires(ordered_random_contract(t0))]
#[requires(sized_float_ordered_sum_contract::<Sequential<T>>(t1, size, bounds))]
#[requires(is_chain_tt(t, t1, t0))]
#[requires(float_in_domain(x@, bounds, Some(size), limit) && float_in_domain(y@, bounds, Some(size), limit))]
#[requires(sym_close(reals(x@), reals(y@), d@))]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[requires(px.permutation_of(x@))]
#[ensures(result.permutation_of(y@))]
#[ensures(real_abs(Sequential::<T>::saturating_sum_logic(px).real()
    - Sequential::<T>::saturating_sum_logic(result).real()) <= o.real())]
pub fn sized_shuffled_match_step<T: Float>(
    t0: CastT<T, SymmetricDistance, InsertDeleteDistance>,
    t1: SumT<T, InsertDeleteDistance>,
    t: SumT<T, SymmetricDistance>,
    size: usize,
    bounds: (T, T),
    limit: usize,
    x: Vec<T>,
    y: Vec<T>,
    d: IntDistance,
    o: T,
    px: Seq<T>,
) -> Seq<T> {
    pearlite! {
        let (lo, hi) = bounds;
        let m = such_that(|m: IntDistance| t0.stability_map.post()[d][Ok(m)] && t1.stability_map.post()[m][Ok(o)]);
        let e = such_that(|e: Real|
            Sequential::<T>::error_bound(size@, Real::from_int(size@) * mag(lo.real(), hi.real()), e)
            && forall<d: IntDistance, o: T> t1.stability_map.post()[d][Ok(o)] ==>
                o.real() >= Real::from_int(d@ / 2) * (hi.real() - lo.real()) + e + e);
        let py = shuffle_match(x@, y@, d@, px);
        shuffled_in_domain(x@, px, bounds, Some(size), limit);
        shuffled_in_domain(y@, py, bounds, Some(size), limit);
        sized_seq_saturating_sum_stable(size, bounds, e, px, py, d@);
        let w = hi.real() - lo.real();
        proof_assert!(w >= Real::from_int(0) && m@ / 2 - d@ / 2 >= 0);
        proof_assert!(Real::from_int(m@ / 2 - d@ / 2) * w >= Real::from_int(0));
        proof_assert!(Real::from_int(m@ / 2) * w == Real::from_int(d@ / 2) * w + Real::from_int(m@ / 2 - d@ / 2) * w);
        proof_assert!(Real::from_int(d@ / 2) * w <= Real::from_int(m@ / 2) * w);
        py
    }
}

/// `make_ordered_random` followed by the sized sequential saturating sum is stable under the
/// symmetric distance, up to the matching of shuffles.
#[logic(prophetic)]
#[ensures(result && forall<t0: CastT<T, SymmetricDistance, InsertDeleteDistance>, t1: SumT<T, InsertDeleteDistance>, t: SumT<T, SymmetricDistance>>
    ordered_random_contract(t0) && sized_seq_ordered_contract(t1, size, bounds)
    && is_chain_tt(t, t1, t0)
    ==> float_sym_shuffled_stable(t, bounds, Some(size), limit))]
pub fn sized_shuffled_float_ordered_lift<T: Float>(
    size: usize,
    bounds: (T, T),
    limit: usize,
) -> bool {
    pearlite! {
        proof_assert!(forall<t0: CastT<T, SymmetricDistance, InsertDeleteDistance>, t1: SumT<T, InsertDeleteDistance>, t: SumT<T, SymmetricDistance>>
            ordered_random_contract(t0) && sized_seq_ordered_contract(t1, size, bounds)
            && is_chain_tt(t, t1, t0) ==>
            (forall<x: Vec<T>> inv(x) && float_in_domain(x@, bounds, Some(size), limit) ==> t.function.pre()[x])
            && (forall<x: Vec<T>, s: T> #[trigger(t.function.post()[x][Ok(s)])] inv(x) && float_in_domain(x@, bounds, Some(size), limit) && t.function.post()[x][Ok(s)] ==>
                shuffled_output(t0, t1, t, bounds, Some(size), limit, x, s))
            && forall<x: Vec<T>, y: Vec<T>, d: IntDistance, o: T, px: Seq<T>>
            #[trigger(t.stability_map.post()[d][Ok(o)], px.permutation_of(x@), sym_close(reals(x@), reals(y@), d@))]
                float_in_domain(x@, bounds, Some(size), limit) && float_in_domain(y@, bounds, Some(size), limit)
                && sym_close(reals(x@), reals(y@), d@)
                && t.stability_map.post()[d][Ok(o)]
                && px.permutation_of(x@)
                ==> {
                    let py = sized_shuffled_match_step(t0, t1, t, size, bounds, limit, x, y, d, o, px);
                    py.permutation_of(y@)
                        && real_abs(Sequential::<T>::saturating_sum_logic(px).real()
                            - Sequential::<T>::saturating_sum_logic(py).real()) <= o.real()
                });
        true
    }
}
