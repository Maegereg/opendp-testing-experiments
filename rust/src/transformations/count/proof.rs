//! Verification of `make_count_by`.
//!
//! The function counts each distinct value, saturating at `TV::MAX`. Under the symmetric distance
//! `d`, `x = c + a` and `y = c + b` as multisets with `|a| + |b| <= d`, so the (saturated) count of
//! each key changes by at most `count(a, k) + count(b, k)`. Summed over any set of distinct keys,
//! this is at most `|a| + |b| <= d`: the L1 distance between the count maps is at most `d`, hence so
//! are the L0 distance (counts are integers) and the L-infinity distance.
use creusot_std::{
    logic::{FMap, Int, real::Real},
    prelude::*,
};

use crate::{
    core::Transformation,
    domains::{AtomDomain, MapDomain, VectorDomain},
    metrics::{AbsoluteDistance, IntDistance, L01InfDistance, SymmetricDistance},
    traits::{Hashable, Integer},
    verification::{
        MaybeDeepModel,
        integer::{int_max, integer_range, integer_real},
        multiset::{
            count, count_concat, count_range, decompose, distinct, kcount, kcount_le_len, sym_close,
        },
    },
};

pub type CountBy<TK, TV> = Transformation<
    VectorDomain<AtomDomain<TK>>,
    SymmetricDistance,
    MapDomain<AtomDomain<TK>, AtomDomain<TV>>,
    L01InfDistance<AbsoluteDistance<TV>>,
>;

/// `c`, saturated at `max`.
#[logic(open)]
pub fn saturate(c: Int, max: Int) -> Int {
    pearlite! { if c <= max { c } else { max } }
}

/// Absolute value of an integer.
#[logic(open)]
pub fn iabs(v: Int) -> Int {
    pearlite! { if v >= 0 { v } else { -v } }
}

/// The count of `k` in `m`, or 0 if `k` is absent (the additive identity, as in the Proof
/// Definition of `L01InfDistance`).
#[logic(open)]
pub fn value<K, TV: Integer>(m: FMap<K, TV>, k: K) -> Int {
    pearlite! { if m.contains(k) { m[k].deep_model() } else { 0 } }
}

/// The L1 distance between `m1` and `m2` restricted to the keys `ks`.
#[logic(open)]
#[variant(ks.len())]
pub fn l1<K, TV: Integer>(ks: Seq<K>, m1: FMap<K, TV>, m2: FMap<K, TV>) -> Int {
    pearlite! {
        if ks.len() == 0 { 0 } else {
            l1(ks.subsequence(0, ks.len() - 1), m1, m2)
                + iabs(value(m1, ks[ks.len() - 1]) - value(m2, ks[ks.len() - 1]))
        }
    }
}

/// The L0 distance between `m1` and `m2` restricted to the keys `ks`: how many counts differ.
#[logic(open)]
#[variant(ks.len())]
pub fn l0<K, TV: Integer>(ks: Seq<K>, m1: FMap<K, TV>, m2: FMap<K, TV>) -> Int {
    pearlite! {
        if ks.len() == 0 { 0 } else {
            l0(ks.subsequence(0, ks.len() - 1), m1, m2)
                + if value(m1, ks[ks.len() - 1]) != value(m2, ks[ks.len() - 1]) { 1 } else { 0 }
        }
    }
}

/// `m` holds the count of every value in `s`, saturating at `TV::MAX`, and no other keys.
#[logic(open)]
pub fn counts_of<K, TV: Integer>(m: FMap<K, TV>, s: Seq<K>) -> bool {
    pearlite! {
        forall<k: K> m.contains(k) == (count(s, k) > 0)
            && (m.contains(k) ==> m[k].deep_model() == saturate(count(s, k), int_max::<TV>()))
    }
}

/// The contract of `make_count_by` on success.
#[logic(open, prophetic)]
pub fn count_by_contract<TK: Hashable + MaybeDeepModel, TV: Integer>(t: CountBy<TK, TV>) -> bool {
    pearlite! {
        // the function can be evaluated on any dataset,
        (forall<x: Vec<TK>> inv(x) ==> t.function.pre()[x])
        // and returns the (saturated) count of each value
        && (forall<x: Vec<TK>, r> t.function.post()[x][r] ==>
            exists<m: std::collections::HashMap<TK, TV>> r == Ok(m) && counts_of(m@, x.deep_model()))
        // the stability map returns at least (d_in, d_in, d_in)
        && (forall<d: IntDistance, o: (IntDistance, TV, TV)> t.stability_map.post()[d][Ok(o)] ==>
            o.0@ >= d@ && o.1.real() >= Real::from_int(d@) && o.2.real() >= Real::from_int(d@))
    }
}

/// Summed over distinct keys, bounded differences give an L1 distance of at most
/// `kcount(ks, a) + kcount(ks, b)`, and the L0 distance is at most the L1 distance.
#[logic]
#[requires(distinct(ks))]
#[requires(forall<k: K> iabs(value(m1, k) - value(m2, k)) <= count(a, k) + count(b, k))]
#[ensures(result && l0(ks, m1, m2) <= l1(ks, m1, m2) && l1(ks, m1, m2) <= kcount(ks, a) + kcount(ks, b))]
#[variant(ks.len())]
pub fn l1_bound<K, TV: Integer>(
    ks: Seq<K>,
    m1: FMap<K, TV>,
    m2: FMap<K, TV>,
    a: Seq<K>,
    b: Seq<K>,
) -> bool {
    pearlite! {
        if ks.len() > 0 {
            proof_assert!(distinct(ks.subsequence(0, ks.len() - 1)));
            l1_bound(ks.subsequence(0, ks.len() - 1), m1, m2, a, b)
        } else {
            true
        }
    }
}

/// Stability of `make_count_by`: on any two datasets within symmetric distance `d`, the count maps
/// are within the stability map at `d` under `L01InfDistance`: for any set of distinct keys, the
/// number of differing counts is at most `d_0`, the sum of the differences at most `d_1`, and each
/// difference at most `d_2`.
#[logic(prophetic)]
#[requires(count_by_contract(t))]
#[requires(sym_close(x.deep_model(), y.deep_model(), d@))]
#[requires(t.function.post()[x][Ok(mx)] && t.function.post()[y][Ok(my)])]
#[requires(t.stability_map.post()[d][Ok(o)])]
#[ensures(forall<k: TK::DeepModelTy> iabs(value(mx@, k) - value(my@, k)) <= o.2.deep_model())]
#[ensures(forall<ks: Seq<TK::DeepModelTy>> distinct(ks) ==>
    l0(ks, mx@, my@) <= o.0@ && l1(ks, mx@, my@) <= o.1.deep_model())]
pub fn count_by_is_stable<TK: Hashable + MaybeDeepModel, TV: Integer>(
    t: CountBy<TK, TV>,
    x: Vec<TK>,
    y: Vec<TK>,
    d: IntDistance,
    mx: std::collections::HashMap<TK, TV>,
    my: std::collections::HashMap<TK, TV>,
    o: (IntDistance, TV, TV),
) {
    pearlite! {
        let (c, a, b) = decompose(x.deep_model(), y.deep_model(), d@);
        count_concat(c, a);
        count_concat(c, b);
        count_range(c);
        count_range(a);
        count_range(b);
        integer_range(o.1);
        integer_real(o.1);
        integer_real(o.2);
        proof_assert!(counts_of(mx@, x.deep_model()) && counts_of(my@, y.deep_model()));
        proof_assert!(forall<k: TK::DeepModelTy>
            value(mx@, k) == saturate(count(c, k) + count(a, k), int_max::<TV>())
            && value(my@, k) == saturate(count(c, k) + count(b, k), int_max::<TV>()));
        proof_assert!(forall<k: TK::DeepModelTy> iabs(value(mx@, k) - value(my@, k)) <= count(a, k) + count(b, k));
        proof_assert!(forall<ks: Seq<TK::DeepModelTy>> distinct(ks) ==>
            l1_bound(ks, mx@, my@, a, b) && kcount_le_len(ks, a) && kcount_le_len(ks, b));
        proof_assert!(forall<k: TK::DeepModelTy> count(a, k) + count(b, k) <= d@);
    }
}
