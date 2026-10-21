//! The insert-delete and symmetric distances, as related by `make_unordered` and
//! `make_ordered_random`.
//!
//! Insert-delete neighbours are symmetric neighbours (`id_close_sym_close`), which justifies
//! `make_unordered`. Conversely, every ordering of a dataset can be matched with an ordering of a
//! symmetric neighbour that is an insert-delete neighbour (`shuffle_match`), which is the
//! combinatorial core of `make_ordered_random`.
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};

use super::{
    RealModel,
    clamped::{decompose, id_close, sub},
    dataset::{count, same, sym_close},
    float::reals,
    ordered,
};
use crate::traits::{Integer, Number};

/// Counts in a concatenation add up.
#[logic]
#[ensures(forall<v: Real> count(a.concat(b), v) == count(a, v) + count(b, v))]
#[variant(b.len())]
pub fn count_concat_all(a: Seq<Real>, b: Seq<Real>) {
    pearlite! {
        if b.len() > 0 {
            proof_assert!(a.concat(b).subsequence(0, a.len() + b.len() - 1)
                == a.concat(b.subsequence(0, b.len() - 1)));
            count_concat_all(a, b.subsequence(0, b.len() - 1))
        } else {
            proof_assert!(a.concat(b).ext_eq(a));
        }
    }
}

/// Deleting `dx` from `x` leaves `z`: as multisets, `x` is `z` plus `dx`.
#[logic]
#[requires(sub(z, x, dx))]
#[ensures(forall<v: Real> count(x, v) == count(z, v) + count(dx, v))]
#[variant(x.len())]
pub fn sub_count(z: Seq<Real>, x: Seq<Real>, dx: Seq<Real>) {
    pearlite! {
        if x.len() > 0 {
            let xi = x.subsequence(0, x.len() - 1);
            if dx.len() > 0 && dx[dx.len() - 1] == x[x.len() - 1] && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                sub_count(z, xi, dx.subsequence(0, dx.len() - 1))
            } else {
                sub_count(z.subsequence(0, z.len() - 1), xi, dx)
            }
        }
    }
}

/// Insert-delete neighbours are symmetric neighbours: the common subsequence is the common
/// sub-multiset, and the deleted and inserted elements are the extra ones.
#[logic]
#[requires(id_close(x, y, d))]
#[ensures(sym_close(x, y, d))]
pub fn id_close_sym_close(x: Seq<Real>, y: Seq<Real>, d: Int) {
    pearlite! {
        let (z, dx, dy) = decompose(x, y, d);
        sub_count(z, x, dx);
        sub_count(z, y, dy);
        count_concat_all(z, dx);
        count_concat_all(z, dy);
        proof_assert!(same(x, z.concat(dx)) && same(y, z.concat(dy)))
    }
}

/// The real values of an integer subsequence form a subsequence of the real values.
#[logic]
#[requires(ordered::sub(z, x, dx))]
#[ensures(sub(reals(z), reals(x), reals(dx)))]
#[variant(x.len())]
pub fn sub_reals<T: Integer>(z: Seq<T>, x: Seq<T>, dx: Seq<T>) {
    pearlite! {
        if x.len() > 0 {
            let xi = x.subsequence(0, x.len() - 1);
            proof_assert!(reals(xi).ext_eq(reals(x).subsequence(0, x.len() - 1)));
            if dx.len() > 0 && dx[dx.len() - 1] == x[x.len() - 1]
                && ordered::sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                let dxi = dx.subsequence(0, dx.len() - 1);
                sub_reals(z, xi, dxi);
                proof_assert!(reals(dxi).ext_eq(reals(dx).subsequence(0, dx.len() - 1)))
            } else {
                let zi = z.subsequence(0, z.len() - 1);
                sub_reals(zi, xi, dx);
                proof_assert!(reals(zi).ext_eq(reals(z).subsequence(0, z.len() - 1)))
            }
        }
    }
}

/// Integer datasets within insert-delete distance `d` are within symmetric distance `d`.
#[logic]
#[requires(ordered::id_close(x, y, d))]
#[ensures(sym_close(reals(x), reals(y), d))]
pub fn int_id_close_sym_close<T: Integer>(x: Seq<T>, y: Seq<T>, d: Int) {
    pearlite! {
        let (z, dx, dy) = such_that(|t: (Seq<T>, Seq<T>, Seq<T>)|
            ordered::sub(t.0, x, t.1) && ordered::sub(t.0, y, t.2) && t.1.len() + t.2.len() <= d);
        sub_reals(z, x, dx);
        sub_reals(z, y, dy);
        proof_assert!(reals(dx).len() + reals(dy).len() <= d);
        id_close_sym_close(reals(x), reals(y), d)
    }
}

/// If `x` and `y` are within symmetric distance `d`, every ordering `px` of `x` can be matched
/// with an ordering of `y` within insert-delete distance `d` of `px`.
///
/// Trusted, not mechanized: delete the extra elements of `x` from `px`, then append the extra
/// elements of `y`. This is the combinatorial step of `make_ordered_random`'s proof. That the
/// matching can be chosen to be a bijection between orderings, so that a uniform shuffle of `x`
/// couples with a uniform shuffle of `y`, is cited from the same proof.
#[trusted]
#[logic(opaque)]
#[requires(sym_close(reals(x), reals(y), d))]
#[requires(px.permutation_of(x))]
#[ensures(result.permutation_of(y) && id_close(reals(px), reals(result), d))]
pub fn shuffle_match<T: RealModel>(x: Seq<T>, y: Seq<T>, d: Int, px: Seq<T>) -> Seq<T> {
    dead
}

/// Cloning a number copies it.
///
/// Trusted: `Number` is implemented by the primitive integers and floats, whose `clone` returns
/// `*self` (creusot-std specifies each, e.g. `impl Clone for f64`), but this cannot be stated for a
/// generic `T`.
#[trusted]
#[logic(opaque)]
#[ensures(forall<a: T, b: T> T::clone.postcondition((&a,), b) ==> a == b)]
pub fn number_clone<T: Number>() {
    dead
}
