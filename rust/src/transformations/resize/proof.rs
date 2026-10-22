//! Verification of `make_resize`.
//!
//! The function pads datasets shorter than `size` with `constant`, and truncates longer ones to
//! their first `size` rows. When the input metric is unordered it shuffles, before padding or
//! truncating (the padded dataset only if the output metric is ordered). Its outputs on `x` are
//! therefore a set of datasets (`resized`), all of them possible.
//!
//! The function may be random, so stability is a coupling: for neighbouring `x` and `y`, the
//! output distributions must be matched so that matched outputs are within the map. A necessary
//! condition is that every possible output of `x` has a possible output of `y` within the map, for
//! every ordered pair (`resize_*_stable`). Where one side is deterministic, this is the coupling.
//! Where both sides shuffle, that the matchings constructed here extend to a coupling of the two
//! shuffles is assumed (`TRUST.md`).
use creusot_std::{
    logic::{Int, such_that},
    prelude::*,
};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::{InsertDeleteDistance, IntDistance, SymmetricDistance},
    traits::{
        CheckAtom,
        samplers::{Shuffle, vec_reorders},
    },
    transformations::IsMetricOrdered,
    verification::{
        multiset::{
            count, count_bounds, count_concat, count_push, decompose, same, same_len, sym_close,
        },
        rows::{EventModel, count_removed, hamming, id_close, id_witness, index_of, sub, sub_same},
    },
};

pub type Resize<TA, MI, MO> =
    Transformation<VectorDomain<AtomDomain<TA>>, MI, VectorDomain<AtomDomain<TA>>, MO>;

/// Cloning an atom copies it.
///
/// Trusted: `CheckAtom` is implemented by the primitive numbers, `bool`, `char`, `String`, `&str`,
/// `IBig`, `RBig` and pairs of floats, all of whose clones are equal to the original. This cannot
/// be stated for a generic `T`.
#[trusted]
#[logic(opaque)]
#[ensures(result && forall<a: T, b: T> T::clone.postcondition((&a,), b) ==> a == b)]
pub fn atom_clone<T: CheckAtom>() -> bool {
    dead
}

/// A permutation has the same elements, with the same multiplicities.
///
/// Trusted: `permutation_of` is Why3's `permut`, equality of the numbers of occurrences of every
/// value, and `same` is equality of `count`, the number of occurrences.
#[trusted]
#[logic(opaque)]
#[ensures(result && forall<a: Seq<T>, b: Seq<T>> a.permutation_of(b) ==> same(a, b))]
pub fn perm_same<T>() -> bool {
    dead
}

/// Shuffling keeps the length.
#[logic]
#[requires(a.reorders(b))]
#[ensures(result && b@.len() == a@.len())]
pub fn shuffle_len<T>(a: Vec<T>, b: Vec<T>) -> bool {
    pearlite! {
        vec_reorders(a, b);
        true
    }
}

/// `n` copies of `c`.
#[logic(open)]
pub fn rep<T>(c: T, n: Int) -> Seq<T> {
    pearlite! { Seq::create(n, |_| c) }
}

/// `y` is a possible output of resizing `x` to `size` rows with `constant`, where
/// `mi_ordered`/`mo_ordered` say whether the input/output metrics are ordered.
///
/// A shuffle may return any ordering (`same`): by its Proof Definition, `Shuffle::shuffle` returns
/// a uniformly random ordering.
#[logic(open)]
pub fn resized<T>(
    mi_ordered: bool,
    mo_ordered: bool,
    x: Seq<T>,
    size: Int,
    constant: T,
    y: Seq<T>,
) -> bool {
    pearlite! {
        if x.len() <= size {
            let p = x.concat(rep(constant, size - x.len()));
            if mo_ordered && !mi_ordered { same(y, p) && y.len() == p.len() } else { y == p }
        } else if mi_ordered {
            y == x.subsequence(0, size)
        } else {
            exists<px: Seq<T>> same(px, x) && px.len() == x.len() && y == px.subsequence(0, size)
        }
    }
}

/// `x` padded with `constant` up to `size` rows.
#[logic(open)]
pub fn padded<T>(x: Seq<T>, size: Int, constant: T) -> Seq<T> {
    pearlite! { x.concat(rep(constant, size - x.len())) }
}

/// What `make_resize`'s function returns on `x`: `x` padded or truncated, after a shuffle where
/// the metrics call for one. `v.reorders(w)` holds only when `w` is the result of shuffling `v`
/// (a uniformly random ordering, by the Proof Definition of `Shuffle`).
#[logic(open)]
pub fn resize_out<T>(
    mi_ordered: bool,
    mo_ordered: bool,
    x: Seq<T>,
    size: Int,
    constant: T,
    y: Seq<T>,
) -> bool {
    pearlite! {
        if x.len() <= size {
            let p = padded(x, size, constant);
            if mo_ordered && !mi_ordered {
                exists<v: Vec<T>, w: Vec<T>> v@ == p && v.reorders(w) && w@ == y
            } else {
                y == p
            }
        } else if mi_ordered {
            y == x.subsequence(0, size)
        } else {
            exists<v: Vec<T>, w: Vec<T>> v@ == x && v.reorders(w) && y == w@.subsequence(0, size)
        }
    }
}

/// The outputs of `make_resize`'s function are among the `resized` datasets. Conversely, since a
/// shuffle returns every ordering with positive probability, every `resized` dataset is a possible
/// output: `resized` is the support of the output distribution.
#[logic]
#[requires(resize_out(mi_ordered, mo_ordered, x, size, constant, y))]
#[ensures(resized(mi_ordered, mo_ordered, x, size, constant, y))]
pub fn out_resized<T>(
    mi_ordered: bool,
    mo_ordered: bool,
    x: Seq<T>,
    size: Int,
    constant: T,
    y: Seq<T>,
) {
    pearlite! {
        proof_assert!(perm_same::<T>());
        proof_assert!(forall<v: Vec<T>, w: Vec<T>> v.reorders(w) ==> {
            vec_reorders(v, w);
            w@.permutation_of(v@) && w@.len() == v@.len()
        });
    }
}

/// The contract of `make_resize` on success.
#[logic(open, prophetic)]
pub fn resize_contract<
    TA: CheckAtom,
    MI: IsMetricOrdered<Distance = IntDistance>,
    MO: IsMetricOrdered<Distance = IntDistance>,
>(
    t: Resize<TA, MI, MO>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    size: usize,
    constant: TA,
) -> bool {
    pearlite! {
        size@ > 0
        // the output domain is the input domain, with `size` rows,
        && t.input_domain.size == input_domain.size
        && t.input_domain.element_domain.deep_model() == input_domain.element_domain.deep_model()
        && t.output_domain.element_domain.deep_model() == input_domain.element_domain.deep_model()
        && t.output_domain.size == Some(size)
        // the function can be evaluated on any dataset,
        && (forall<x: Vec<TA>> inv(x) ==> t.function.pre()[x])
        // and returns one of the resized datasets,
        && (forall<x: Vec<TA>, y: Vec<TA>> t.function.post()[x][Ok(y)] ==>
            resize_out(MI::ORDERED, MO::ORDERED, x@, size@, constant, y@))
        // the stability map returns at least 2 d_in
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= 2 * d@)
    }
}

// ---------------------------------------------------------------------------------------------
// Sequences as multisets
// ---------------------------------------------------------------------------------------------

/// Occurrences in `n` copies of `c`.
#[logic]
#[requires(n >= 0)]
#[ensures(forall<v: T> count(rep(c, n), v) == if v == c { n } else { 0 })]
#[ensures(rep(c, n).len() == n)]
#[variant(n)]
pub fn count_rep<T>(c: T, n: Int) {
    pearlite! {
        if n > 0 {
            proof_assert!(rep(c, n).subsequence(0, n - 1).ext_eq(rep(c, n - 1)));
            count_rep(c, n - 1)
        }
    }
}

/// `n + m` copies are `n` copies followed by `m` copies.
#[logic]
#[requires(n >= 0 && m >= 0)]
#[ensures(rep(c, n + m) == rep(c, n).concat(rep(c, m)))]
pub fn rep_concat<T>(c: T, n: Int, m: Int) {
    pearlite! { proof_assert!(rep(c, n + m).ext_eq(rep(c, n).concat(rep(c, m)))) }
}

/// A common subsequence of two sequences of the same length, keeping the positions where they
/// agree: each side deletes `hamming(p, q)` elements.
#[logic]
#[requires(p.len() == q.len())]
#[ensures(sub(result.0, p, result.1) && sub(result.0, q, result.2))]
#[ensures(result.1.len() == hamming(p, q) && result.2.len() == hamming(p, q))]
#[variant(p.len())]
pub fn hamming_sub<T>(p: Seq<T>, q: Seq<T>) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        if p.len() == 0 {
            (Seq::empty(), Seq::empty(), Seq::empty())
        } else {
            let n = p.len();
            let (z, ep, eq) = hamming_sub(p.subsequence(0, n - 1), q.subsequence(0, n - 1));
            if p[n - 1] == q[n - 1] {
                proof_assert!(z.push_back(p[n - 1]).subsequence(0, z.len()).ext_eq(z));
                (z.push_back(p[n - 1]), ep, eq)
            } else {
                proof_assert!(ep.push_back(p[n - 1]).subsequence(0, ep.len()).ext_eq(ep));
                proof_assert!(eq.push_back(q[n - 1]).subsequence(0, eq.len()).ext_eq(eq));
                (z, ep.push_back(p[n - 1]), eq.push_back(q[n - 1]))
            }
        }
    }
}

/// Sequences of the same length that differ in `e` positions are within insert-delete distance
/// `2 e`.
#[logic]
#[requires(p.len() == q.len() && hamming(p, q) <= e)]
#[ensures(result && id_close(p, q, 2 * e))]
pub fn hamming_id<T>(p: Seq<T>, q: Seq<T>, e: Int) -> bool {
    pearlite! {
        let (z, ep, eq) = hamming_sub(p, q);
        true
    }
}

/// If `p` consists of `c` and `a`, and `b` has as many elements as `a`, then some ordering of `c`
/// and `b` agrees with `p` everywhere except at (at most) `|a|` positions: keep each element of
/// `c` where it is in `p`, and put the elements of `b` in the positions of those of `a`.
#[logic]
#[requires(same(p, c.concat(a)) && a.len() == b.len())]
#[ensures(same(result, c.concat(b)) && result.len() == p.len() && hamming(p, result) <= a.len())]
#[variant(p.len())]
pub fn reorder<T>(p: Seq<T>, c: Seq<T>, a: Seq<T>, b: Seq<T>) -> Seq<T> {
    pearlite! {
        if p.len() == 0 {
            same_len(p, c.concat(a));
            proof_assert!(c.concat(b).len() == 0);
            Seq::empty()
        } else {
            let n = p.len();
            let v = p[n - 1];
            let pi = p.subsequence(0, n - 1);
            count_push(pi, v);
            proof_assert!(p == pi.push_back(v));
            count_bounds(pi, v);
            count_concat(c, a);
            count_concat(c, b);
            if count(c, v) > 0 {
                let j = index_of(c, v);
                let c2 = c.removed(j);
                count_removed(c, j);
                count_concat(c2, a);
                count_concat(c2, b);
                let q = reorder(pi, c2, a, b);
                count_push(q, v);
                q.push_back(v)
            } else {
                let j = index_of(a, v);
                let a2 = a.removed(j);
                count_removed(a, j);
                count_concat(c, a2);
                let bi = b.subsequence(0, b.len() - 1);
                let w = b[b.len() - 1];
                count_push(bi, w);
                proof_assert!(b == bi.push_back(w));
                count_concat(c, bi);
                let q = reorder(pi, c, a2, bi);
                count_push(q, w);
                q.push_back(w)
            }
        }
    }
}

/// If `u ++ w` consists of `c` and `a`, then `u` consists of parts of `c` and `a`, and `w` of
/// the rest.
#[logic]
#[requires(same(u.concat(w), c.concat(a)))]
#[ensures(same(u, result.0.concat(result.1)) && same(w, result.2.concat(result.3)))]
#[ensures(same(c, result.0.concat(result.2)) && same(a, result.1.concat(result.3)))]
#[variant(u.len())]
pub fn split<T>(u: Seq<T>, w: Seq<T>, c: Seq<T>, a: Seq<T>) -> (Seq<T>, Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        if u.len() == 0 {
            proof_assert!(u.concat(w).ext_eq(w));
            proof_assert!(Seq::<T>::empty().concat(c).ext_eq(c));
            proof_assert!(Seq::<T>::empty().concat(a).ext_eq(a));
            (Seq::empty(), Seq::empty(), c, a)
        } else {
            let n = u.len();
            let v = u[n - 1];
            let ui = u.subsequence(0, n - 1);
            count_push(ui, v);
            proof_assert!(u == ui.push_back(v));
            count_bounds(ui, v);
            count_concat(u, w);
            count_concat(ui, w);
            count_concat(c, a);
            if count(c, v) > 0 {
                let j = index_of(c, v);
                let c2 = c.removed(j);
                count_removed(c, j);
                count_concat(c2, a);
                let (c1, a1, cw, aw) = split(ui, w, c2, a);
                count_push(c1, v);
                count_concat(c1.push_back(v), a1);
                count_concat(c1, a1);
                count_concat(c1.push_back(v), cw);
                count_concat(c1, cw);
                (c1.push_back(v), a1, cw, aw)
            } else {
                let j = index_of(a, v);
                let a2 = a.removed(j);
                count_removed(a, j);
                count_concat(c, a2);
                let (c1, a1, cw, aw) = split(ui, w, c, a2);
                count_push(a1, v);
                count_concat(c1, a1.push_back(v));
                count_concat(c1, a1);
                count_concat(a1.push_back(v), aw);
                count_concat(a1, aw);
                (c1, a1.push_back(v), cw, aw)
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Subsequences and prefixes
// ---------------------------------------------------------------------------------------------

/// The first `s` elements of `x` hold a prefix of the subsequence `z`, of length `k`, and
/// `s - k` deleted elements, at most as many as were deleted in all of `x`.
#[logic]
#[requires(sub(z, x, dx) && 0 <= s && s <= x.len())]
#[ensures(0 <= result.0 && result.0 <= z.len())]
#[ensures(sub(z.subsequence(0, result.0), x.subsequence(0, s), result.1))]
#[ensures(result.1.len() == s - result.0 && result.1.len() <= dx.len())]
#[ensures(z.len() - result.0 <= x.len() - s)]
#[variant(x.len())]
pub fn sub_prefix<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>, s: Int) -> (Int, Seq<T>) {
    pearlite! {
        if s == x.len() {
            sub_same(z, x, dx);
            proof_assert!(z.subsequence(0, z.len()).ext_eq(z));
            proof_assert!(x.subsequence(0, s).ext_eq(x));
            (z.len(), dx)
        } else {
            let xi = x.subsequence(0, x.len() - 1);
            proof_assert!(xi.subsequence(0, s).ext_eq(x.subsequence(0, s)));
            if dx.len() > 0 && dx[dx.len() - 1] == x[x.len() - 1]
                && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
                sub_prefix(z, xi, dx.subsequence(0, dx.len() - 1), s)
            } else {
                let zi = z.subsequence(0, z.len() - 1);
                let r = sub_prefix(zi, xi, dx, s);
                proof_assert!(zi.subsequence(0, r.0).ext_eq(z.subsequence(0, r.0)));
                r
            }
        }
    }
}

/// Deleting the last element of a subsequence.
#[logic]
#[requires(sub(z, x, dx) && z.len() > 0)]
#[ensures(sub(z.subsequence(0, z.len() - 1), x, result) && result.len() == dx.len() + 1)]
#[variant(x.len())]
pub fn sub_drop1<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>) -> Seq<T> {
    pearlite! {
        sub_same(z, x, dx);
        let xi = x.subsequence(0, x.len() - 1);
        let xl = x[x.len() - 1];
        if dx.len() > 0 && dx[dx.len() - 1] == xl && sub(z, xi, dx.subsequence(0, dx.len() - 1)) {
            let e = sub_drop1(z, xi, dx.subsequence(0, dx.len() - 1));
            proof_assert!(e.push_back(xl).subsequence(0, e.len()).ext_eq(e));
            e.push_back(xl)
        } else {
            proof_assert!(dx.push_back(xl).subsequence(0, dx.len()).ext_eq(dx));
            dx.push_back(xl)
        }
    }
}

/// Deleting the last elements of a subsequence, keeping its first `j`.
#[logic]
#[requires(sub(z, x, dx) && 0 <= j && j <= z.len())]
#[ensures(sub(z.subsequence(0, j), x, result) && result.len() == dx.len() + z.len() - j)]
#[variant(z.len() - j)]
pub fn sub_drop<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>, j: Int) -> Seq<T> {
    pearlite! {
        if j == z.len() {
            proof_assert!(z.subsequence(0, j).ext_eq(z));
            dx
        } else {
            let e = sub_drop1(z, x, dx);
            let zi = z.subsequence(0, z.len() - 1);
            proof_assert!(zi.subsequence(0, j).ext_eq(z.subsequence(0, j)));
            sub_drop(zi, x, e, j)
        }
    }
}

/// The first `s` elements of two datasets within insert-delete distance `d` are within `2 d`.
#[logic]
#[requires(id_close(x, y, d) && 0 <= s && s <= x.len() && s <= y.len())]
#[ensures(result && id_close(x.subsequence(0, s), y.subsequence(0, s), 2 * d))]
pub fn id_prefix<T>(x: Seq<T>, y: Seq<T>, d: Int, s: Int) -> bool {
    pearlite! {
        let (z, dx, dy) = such_that(|w: (Seq<T>, Seq<T>, Seq<T>)|
            sub(w.0, x, w.1) && sub(w.0, y, w.2) && w.1.len() + w.2.len() <= d);
        let (kx, ex) = sub_prefix(z, x, dx, s);
        let (ky, ey) = sub_prefix(z, y, dy, s);
        let k = if kx <= ky { kx } else { ky };
        proof_assert!(z.subsequence(0, kx).subsequence(0, k).ext_eq(z.subsequence(0, k)));
        proof_assert!(z.subsequence(0, ky).subsequence(0, k).ext_eq(z.subsequence(0, k)));
        let fx = sub_drop(z.subsequence(0, kx), x.subsequence(0, s), ex, k);
        let fy = sub_drop(z.subsequence(0, ky), y.subsequence(0, s), ey, k);
        proof_assert!(fx.len() == s - k && fy.len() == s - k);
        true
    }
}

// ---------------------------------------------------------------------------------------------
// Matching resized datasets
// ---------------------------------------------------------------------------------------------

/// Two padded datasets: `x = c a` and `y = c b` (as multisets) give `pad(x) = c' a'` and
/// `pad(y) = c' b'` with `|a'| = |b'| = max(|a|, |b|)`, the shared padding moving into `c'`.
#[logic]
#[requires(same(x, c.concat(a)) && same(y, c.concat(b)))]
#[requires(x.len() <= size && y.len() <= size)]
#[ensures(same(padded(x, size, k), result.0.concat(result.1)))]
#[ensures(same(padded(y, size, k), result.0.concat(result.2)))]
#[ensures(result.1.len() == result.2.len() && result.1.len() <= a.len() + b.len())]
pub fn match_pad_pad<T>(
    x: Seq<T>,
    y: Seq<T>,
    c: Seq<T>,
    a: Seq<T>,
    b: Seq<T>,
    size: Int,
    k: T,
) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        same_len(x, c.concat(a));
        same_len(y, c.concat(b));
        let k1 = size - x.len();
        let k2 = size - y.len();
        let m = if k1 <= k2 { k1 } else { k2 };
        let c2 = c.concat(rep(k, m));
        let a2 = a.concat(rep(k, k1 - m));
        let b2 = b.concat(rep(k, k2 - m));
        count_rep(k, k1);
        count_rep(k, k2);
        count_rep(k, m);
        count_rep(k, k1 - m);
        count_rep(k, k2 - m);
        count_concat(x, rep(k, k1));
        count_concat(y, rep(k, k2));
        count_concat(c, a);
        count_concat(c, b);
        count_concat(c, rep(k, m));
        count_concat(a, rep(k, k1 - m));
        count_concat(b, rep(k, k2 - m));
        count_concat(c2, a2);
        count_concat(c2, b2);
        (c2, a2, b2)
    }
}

/// Both truncated, the first `s` rows of an ordering `px` of `x = c a` are matched with `s` rows
/// `t` of `y = c b`: `px[..s] = c1 a1` and `t = c1 b1` with `|b1| = |a1| <= |a|`, and the rest
/// of `y` is `r`.
#[logic]
#[requires(same(px, c.concat(a)) && same(y, c.concat(b)))]
#[requires(0 <= s && s < px.len() && s < y.len())]
#[ensures(same(px.subsequence(0, s), result.0.concat(result.1)))]
#[ensures(same(y, result.0.concat(result.2).concat(result.3)))]
#[ensures(result.1.len() == result.2.len() && result.1.len() <= a.len())]
pub fn match_trunc_trunc<T>(
    px: Seq<T>,
    y: Seq<T>,
    c: Seq<T>,
    a: Seq<T>,
    b: Seq<T>,
    s: Int,
) -> (Seq<T>, Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        let u = px.subsequence(0, s);
        let w = px.subsequence(s, px.len());
        proof_assert!(u.concat(w).ext_eq(px));
        let (c1, a1, c2, a2) = split(u, w, c, a);
        same_len(u, c1.concat(a1));
        same_len(c, c1.concat(c2));
        same_len(a, a1.concat(a2));
        same_len(y, c.concat(b));
        let v = c2.concat(b);
        proof_assert!(u.len() == s && c1.len() + a1.len() == s);
        proof_assert!(v.len() == y.len() - c1.len() && a1.len() <= v.len());
        let b1 = v.subsequence(0, a1.len());
        let r = v.subsequence(a1.len(), v.len());
        proof_assert!(b1.concat(r).ext_eq(v));
        count_concat(c, b);
        count_concat(c1, c2);
        count_concat(c2, b);
        count_concat(b1, r);
        count_concat(c1, b1);
        count_concat(c1.concat(b1), r);
        (c1, a1, b1, r)
    }
}

/// `x` truncated and `y` padded: the first `s` rows of an ordering `px` of `x = c a` are
/// `c1 a1`, and `pad(y) = c1 b1` with `|b1| = |a1| <= |a|`.
#[logic]
#[requires(same(px, c.concat(a)) && same(y, c.concat(b)))]
#[requires(0 <= s && s < px.len() && y.len() <= s)]
#[ensures(same(px.subsequence(0, s), result.0.concat(result.1)))]
#[ensures(same(padded(y, s, k), result.0.concat(result.2)))]
#[ensures(result.1.len() == result.2.len() && result.1.len() <= a.len())]
pub fn match_trunc_pad<T>(
    px: Seq<T>,
    y: Seq<T>,
    c: Seq<T>,
    a: Seq<T>,
    b: Seq<T>,
    s: Int,
    k: T,
) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        let u = px.subsequence(0, s);
        let w = px.subsequence(s, px.len());
        proof_assert!(u.concat(w).ext_eq(px));
        let (c1, a1, c2, a2) = split(u, w, c, a);
        same_len(u, c1.concat(a1));
        same_len(c, c1.concat(c2));
        same_len(y, c.concat(b));
        count_rep(k, s - y.len());
        let b1 = c2.concat(b).concat(rep(k, s - y.len()));
        count_concat(y, rep(k, s - y.len()));
        count_concat(c, b);
        count_concat(c1, c2);
        count_concat(c2, b);
        count_concat(c2.concat(b), rep(k, s - y.len()));
        count_concat(c1, b1);
        (c1, a1, b1)
    }
}

/// `x` padded and `y` truncated (symmetric distance): with `x = c a` and `y = c b`,
/// `pad(x) = c a'` and `y = c b' r` with `|a'| = |b'| < |b|`.
#[logic]
#[requires(same(x, c.concat(a)) && same(y, c.concat(b)))]
#[requires(x.len() <= s && s < y.len())]
#[ensures(same(padded(x, s, k), c.concat(result.0)))]
#[ensures(same(y, c.concat(result.1).concat(result.2)))]
#[ensures(result.0.len() == result.1.len() && result.0.len() < b.len())]
pub fn match_pad_trunc<T>(
    x: Seq<T>,
    y: Seq<T>,
    c: Seq<T>,
    a: Seq<T>,
    b: Seq<T>,
    s: Int,
    k: T,
) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        same_len(x, c.concat(a));
        same_len(y, c.concat(b));
        let n = a.len() + s - x.len();
        count_rep(k, s - x.len());
        let a2 = a.concat(rep(k, s - x.len()));
        let b2 = b.subsequence(0, n);
        let r = b.subsequence(n, b.len());
        proof_assert!(b2.concat(r).ext_eq(b));
        proof_assert!(c.concat(b2).concat(r).ext_eq(c.concat(b)));
        count_concat(x, rep(k, s - x.len()));
        count_concat(c, a);
        count_concat(a, rep(k, s - x.len()));
        count_concat(c, a2);
        (a2, b2, r)
    }
}

/// `x` padded and `y` truncated (insert-delete distance): with `x` and `y` obtained from a common
/// subsequence `z` by inserting `dx` and `dy`, `pad(x) = c a` and `y[..s] = c b` with
/// `|a| = |b| <= |dy|`.
#[logic]
#[requires(sub(z, x, dx) && sub(z, y, dy))]
#[requires(x.len() <= s && s < y.len())]
#[ensures(same(padded(x, s, k), result.0.concat(result.1)))]
#[ensures(same(y.subsequence(0, s), result.0.concat(result.2)))]
#[ensures(result.1.len() == result.2.len() && result.1.len() <= dy.len())]
pub fn match_id_pad_trunc<T>(
    z: Seq<T>,
    x: Seq<T>,
    dx: Seq<T>,
    y: Seq<T>,
    dy: Seq<T>,
    s: Int,
    k: T,
) -> (Seq<T>, Seq<T>, Seq<T>) {
    pearlite! {
        sub_same(z, x, dx);
        sub_same(z, y, dy);
        let (j, ey) = sub_prefix(z, y, dy, s);
        let zj = z.subsequence(0, j);
        sub_same(zj, y.subsequence(0, s), ey);
        let zr = z.subsequence(j, z.len());
        proof_assert!(zj.concat(zr).ext_eq(z));
        count_rep(k, s - x.len());
        let a = zr.concat(dx).concat(rep(k, s - x.len()));
        count_concat(x, rep(k, s - x.len()));
        count_concat(z, dx);
        count_concat(zj, zr);
        count_concat(zr, dx);
        count_concat(zr.concat(dx), rep(k, s - x.len()));
        count_concat(zj, a);
        (zj, a, ey)
    }
}

/// The insert-delete distance only grows with `d`.
#[logic]
#[requires(id_close(x, y, d) && d <= e)]
#[ensures(result && id_close(x, y, e))]
pub fn id_mono<T>(x: Seq<T>, y: Seq<T>, d: Int, e: Int) -> bool {
    true
}

/// Datasets within insert-delete distance `d` are within symmetric distance `d`, with the
/// common subsequence as the common part.
#[logic]
#[requires(sub(z, x, dx) && sub(z, y, dy))]
#[ensures(result && same(x, z.concat(dx)) && same(y, z.concat(dy)) && sym_close(x, y, dx.len() + dy.len()))]
pub fn id_sym<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>, y: Seq<T>, dy: Seq<T>) -> bool {
    pearlite! {
        sub_same(z, x, dx);
        sub_same(z, y, dy);
        true
    }
}

/// `make_resize` from `SymmetricDistance` to `SymmetricDistance`: every output `fx` of `x` is
/// matched with an output of `y` within symmetric distance `2 d`.
#[logic]
#[requires(sym_close(x, y, d) && 0 <= s)]
#[requires(resized(false, false, x, s, k, fx))]
#[ensures(resized(false, false, y, s, k, result) && sym_close(fx, result, 2 * d))]
pub fn match_sym_sym<T>(x: Seq<T>, y: Seq<T>, d: Int, s: Int, k: T, fx: Seq<T>) -> Seq<T> {
    pearlite! {
        let (c, a, b) = decompose(x, y, d);
        same_len(x, c.concat(a));
        same_len(y, c.concat(b));
        if x.len() <= s && y.len() <= s {
            let (c2, a2, b2) = match_pad_pad(x, y, c, a, b, s, k);
            padded(y, s, k)
        } else if x.len() <= s {
            let (a2, b2, r) = match_pad_trunc(x, y, c, a, b, s, k);
            same_len(padded(x, s, k), c.concat(a2));
            let py = c.concat(b2).concat(r);
            same_len(y, py);
            proof_assert!(py.subsequence(0, s).ext_eq(c.concat(b2)));
            c.concat(b2)
        } else {
            let px = such_that(|px: Seq<T>| same(px, x) && px.len() == x.len() && fx == px.subsequence(0, s));
            if y.len() <= s {
                let (c1, a1, b1) = match_trunc_pad(px, y, c, a, b, s, k);
                padded(y, s, k)
            } else {
                let (c1, a1, b1, r) = match_trunc_trunc(px, y, c, a, b, s);
                same_len(fx, c1.concat(a1));
                let py = c1.concat(b1).concat(r);
                same_len(y, py);
                proof_assert!(py.subsequence(0, s).ext_eq(c1.concat(b1)));
                c1.concat(b1)
            }
        }
    }
}

/// `make_resize` from `SymmetricDistance` to `InsertDeleteDistance`: every output `fx` of `x` is
/// matched with an output of `y` within insert-delete distance `2 d`.
#[logic]
#[requires(sym_close(x, y, d) && 0 <= s)]
#[requires(resized(false, true, x, s, k, fx))]
#[ensures(resized(false, true, y, s, k, result) && id_close(fx, result, 2 * d))]
pub fn match_sym_id<T>(x: Seq<T>, y: Seq<T>, d: Int, s: Int, k: T, fx: Seq<T>) -> Seq<T> {
    pearlite! {
        let (c, a, b) = decompose(x, y, d);
        same_len(x, c.concat(a));
        same_len(y, c.concat(b));
        if x.len() <= s && y.len() <= s {
            let (c2, a2, b2) = match_pad_pad(x, y, c, a, b, s, k);
            let q = reorder(fx, c2, a2, b2);
            same_len(padded(y, s, k), c2.concat(b2));
            hamming_id(fx, q, a2.len());
            id_mono(fx, q, 2 * a2.len(), 2 * d);
            q
        } else if x.len() <= s {
            let (a2, b2, r) = match_pad_trunc(x, y, c, a, b, s, k);
            let q = reorder(fx, c, a2, b2);
            count_concat(q, r);
            count_concat(c, b2);
            count_concat(c.concat(b2), r);
            let py = q.concat(r);
            same_len(y, py);
            proof_assert!(py.subsequence(0, s).ext_eq(q));
            hamming_id(fx, q, a2.len());
            id_mono(fx, q, 2 * a2.len(), 2 * d);
            q
        } else {
            let px = such_that(|px: Seq<T>| same(px, x) && px.len() == x.len() && fx == px.subsequence(0, s));
            if y.len() <= s {
                let (c1, a1, b1) = match_trunc_pad(px, y, c, a, b, s, k);
                let q = reorder(fx, c1, a1, b1);
                same_len(padded(y, s, k), c1.concat(b1));
                hamming_id(fx, q, a1.len());
                id_mono(fx, q, 2 * a1.len(), 2 * d);
                q
            } else {
                let (c1, a1, b1, r) = match_trunc_trunc(px, y, c, a, b, s);
                let q = reorder(fx, c1, a1, b1);
                count_concat(q, r);
                count_concat(c1, b1);
                count_concat(c1.concat(b1), r);
                let py = q.concat(r);
                same_len(y, py);
                proof_assert!(py.subsequence(0, s).ext_eq(q));
                hamming_id(fx, q, a1.len());
                id_mono(fx, q, 2 * a1.len(), 2 * d);
                q
            }
        }
    }
}

/// `make_resize` from `InsertDeleteDistance` to `SymmetricDistance`: the function is
/// deterministic, and the outputs of `x` and `y` are within symmetric distance `2 d`.
#[logic]
#[requires(id_close(x, y, d) && 0 <= s)]
#[requires(resized(true, false, x, s, k, fx))]
#[ensures(resized(true, false, y, s, k, result) && sym_close(fx, result, 2 * d))]
pub fn match_id_sym<T>(x: Seq<T>, y: Seq<T>, d: Int, s: Int, k: T, fx: Seq<T>) -> Seq<T> {
    pearlite! {
        let (z, dx, dy) = id_witness(x, y, d);
        id_sym(z, x, dx, y, dy);
        if x.len() <= s && y.len() <= s {
            let (c2, a2, b2) = match_pad_pad(x, y, z, dx, dy, s, k);
            proof_assert!(fx == padded(x, s, k));
            proof_assert!(sym_close(fx, padded(y, s, k), 2 * d));
            padded(y, s, k)
        } else if x.len() <= s {
            let (c, a, b) = match_id_pad_trunc(z, x, dx, y, dy, s, k);
            proof_assert!(fx == padded(x, s, k));
            proof_assert!(sym_close(fx, y.subsequence(0, s), 2 * d));
            y.subsequence(0, s)
        } else if y.len() <= s {
            let (c, a, b) = match_id_pad_trunc(z, y, dy, x, dx, s, k);
            proof_assert!(fx == x.subsequence(0, s));
            proof_assert!(sym_close(fx, padded(y, s, k), 2 * d));
            padded(y, s, k)
        } else {
            id_prefix(x, y, d, s);
            let fy = y.subsequence(0, s);
            let (z2, ex, ey) = id_witness(fx, fy, 2 * d);
            id_sym(z2, fx, ex, fy, ey);
            fy
        }
    }
}

/// Appending the same elements to a sequence and to its subsequence.
#[logic]
#[requires(sub(z, x, dx))]
#[ensures(sub(z.concat(w), x.concat(w), dx))]
#[variant(w.len())]
pub fn sub_append_common<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>, w: Seq<T>) {
    pearlite! {
        if w.len() > 0 {
            let wi = w.subsequence(0, w.len() - 1);
            sub_append_common(z, x, dx, wi);
            proof_assert!(z.concat(w).subsequence(0, z.len() + wi.len()).ext_eq(z.concat(wi)));
            proof_assert!(x.concat(w).subsequence(0, x.len() + wi.len()).ext_eq(x.concat(wi)));
        } else {
            proof_assert!(z.concat(w).ext_eq(z) && x.concat(w).ext_eq(x));
        }
    }
}

/// Appending elements to a sequence, as deletions.
#[logic]
#[requires(sub(z, x, dx))]
#[ensures(sub(z, x.concat(v), dx.concat(v)))]
#[variant(v.len())]
pub fn sub_append_del<T>(z: Seq<T>, x: Seq<T>, dx: Seq<T>, v: Seq<T>) {
    pearlite! {
        if v.len() > 0 {
            let vi = v.subsequence(0, v.len() - 1);
            sub_append_del(z, x, dx, vi);
            proof_assert!(x.concat(v).subsequence(0, x.len() + vi.len()).ext_eq(x.concat(vi)));
            proof_assert!(dx.concat(v).subsequence(0, dx.len() + vi.len()).ext_eq(dx.concat(vi)));
        } else {
            proof_assert!(x.concat(v).ext_eq(x) && dx.concat(v).ext_eq(dx));
        }
    }
}

/// Insert-delete closeness is symmetric.
#[logic]
#[requires(id_close(x, y, d))]
#[ensures(result && id_close(y, x, d))]
pub fn id_swap<T>(x: Seq<T>, y: Seq<T>, d: Int) -> bool {
    pearlite! {
        let (z, dx, dy) = id_witness(x, y, d);
        true
    }
}

/// Padding both datasets at the end: the shared padding extends the common subsequence, and the
/// rest is deleted, `max(|dx|, |dy|)` elements on each side.
#[logic]
#[requires(sub(z, x, dx) && sub(z, y, dy) && x.len() <= s && y.len() <= s)]
#[ensures(result && id_close(padded(x, s, k), padded(y, s, k), 2 * (dx.len() + dy.len())))]
pub fn id_pad_pad<T>(
    z: Seq<T>,
    x: Seq<T>,
    dx: Seq<T>,
    y: Seq<T>,
    dy: Seq<T>,
    s: Int,
    k: T,
) -> bool {
    pearlite! {
        sub_same(z, x, dx);
        sub_same(z, y, dy);
        let k1 = s - x.len();
        let k2 = s - y.len();
        let m = if k1 <= k2 { k1 } else { k2 };
        count_rep(k, m);
        count_rep(k, k1 - m);
        count_rep(k, k2 - m);
        rep_concat(k, m, k1 - m);
        rep_concat(k, m, k2 - m);
        let zm = z.concat(rep(k, m));
        sub_append_common(z, x, dx, rep(k, m));
        sub_append_common(z, y, dy, rep(k, m));
        sub_append_del(zm, x.concat(rep(k, m)), dx, rep(k, k1 - m));
        sub_append_del(zm, y.concat(rep(k, m)), dy, rep(k, k2 - m));
        proof_assert!(x.concat(rep(k, m)).concat(rep(k, k1 - m)).ext_eq(padded(x, s, k)));
        proof_assert!(y.concat(rep(k, m)).concat(rep(k, k2 - m)).ext_eq(padded(y, s, k)));
        true
    }
}

/// Padding `x` and truncating `y` to `s` rows: a prefix of the common subsequence remains, with
/// at most `|dy|` deletions on each side.
#[logic]
#[requires(sub(z, x, dx) && sub(z, y, dy) && x.len() <= s && s <= y.len())]
#[ensures(result && id_close(padded(x, s, k), y.subsequence(0, s), 2 * dy.len()))]
pub fn id_pad_trunc<T>(
    z: Seq<T>,
    x: Seq<T>,
    dx: Seq<T>,
    y: Seq<T>,
    dy: Seq<T>,
    s: Int,
    k: T,
) -> bool {
    pearlite! {
        sub_same(z, x, dx);
        sub_same(z, y, dy);
        let (j, ey) = sub_prefix(z, y, dy, s);
        let e1 = sub_drop(z, x, dx, j);
        count_rep(k, s - x.len());
        sub_append_del(z.subsequence(0, j), x, e1, rep(k, s - x.len()));
        proof_assert!(e1.concat(rep(k, s - x.len())).len() == s - j);
        true
    }
}

/// `make_resize` from `InsertDeleteDistance` to `InsertDeleteDistance`: the function is
/// deterministic, and the outputs of `x` and `y` are within insert-delete distance `2 d`.
#[logic]
#[requires(id_close(x, y, d) && 0 <= s)]
#[requires(resized(true, true, x, s, k, fx))]
#[ensures(resized(true, true, y, s, k, result) && id_close(fx, result, 2 * d))]
pub fn match_id_id<T>(x: Seq<T>, y: Seq<T>, d: Int, s: Int, k: T, fx: Seq<T>) -> Seq<T> {
    pearlite! {
        let (z, dx, dy) = id_witness(x, y, d);
        if x.len() <= s && y.len() <= s {
            id_pad_pad(z, x, dx, y, dy, s, k);
            id_mono(fx, padded(y, s, k), 2 * (dx.len() + dy.len()), 2 * d);
            padded(y, s, k)
        } else if x.len() <= s {
            id_pad_trunc(z, x, dx, y, dy, s, k);
            id_mono(fx, y.subsequence(0, s), 2 * dy.len(), 2 * d);
            y.subsequence(0, s)
        } else if y.len() <= s {
            id_pad_trunc(z, y, dy, x, dx, s, k);
            id_swap(padded(y, s, k), fx, 2 * dx.len());
            id_mono(fx, padded(y, s, k), 2 * dx.len(), 2 * d);
            padded(y, s, k)
        } else {
            id_prefix(x, y, d, s);
            y.subsequence(0, s)
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Stability of `make_resize`, per pair of metrics
// ---------------------------------------------------------------------------------------------

/// `make_resize` from `SymmetricDistance` to `SymmetricDistance` is stable: every output of `x`
/// is matched with an output of a `d`-close `y` within the map.
#[logic(prophetic)]
#[requires(resize_contract(t, input_domain, size, constant))]
#[requires(<SymmetricDistance as EventModel>::close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(fx)] && t.stability_map.post()[d][Ok(o)])]
#[ensures(resized(<SymmetricDistance as IsMetricOrdered>::ORDERED, <SymmetricDistance as IsMetricOrdered>::ORDERED,
    y@, size@, constant, result))]
#[ensures(<SymmetricDistance as EventModel>::close(fx@, result, o@))]
pub fn resize_sym_sym_stable<TA: CheckAtom>(
    t: Resize<TA, SymmetricDistance, SymmetricDistance>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    size: usize,
    constant: TA,
    x: Vec<TA>,
    y: Vec<TA>,
    d: IntDistance,
    fx: Vec<TA>,
    o: IntDistance,
) -> Seq<TA> {
    pearlite! {
        out_resized(<SymmetricDistance as IsMetricOrdered>::ORDERED, <SymmetricDistance as IsMetricOrdered>::ORDERED, x@, size@, constant, fx@);
        match_sym_sym(x@, y@, d@, size@, constant, fx@)
    }
}

/// `make_resize` from `SymmetricDistance` to `InsertDeleteDistance` is stable.
#[logic(prophetic)]
#[requires(resize_contract(t, input_domain, size, constant))]
#[requires(<SymmetricDistance as EventModel>::close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(fx)] && t.stability_map.post()[d][Ok(o)])]
#[ensures(resized(<SymmetricDistance as IsMetricOrdered>::ORDERED, <InsertDeleteDistance as IsMetricOrdered>::ORDERED,
    y@, size@, constant, result))]
#[ensures(<InsertDeleteDistance as EventModel>::close(fx@, result, o@))]
pub fn resize_sym_id_stable<TA: CheckAtom>(
    t: Resize<TA, SymmetricDistance, InsertDeleteDistance>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    size: usize,
    constant: TA,
    x: Vec<TA>,
    y: Vec<TA>,
    d: IntDistance,
    fx: Vec<TA>,
    o: IntDistance,
) -> Seq<TA> {
    pearlite! {
        out_resized(<SymmetricDistance as IsMetricOrdered>::ORDERED, <InsertDeleteDistance as IsMetricOrdered>::ORDERED, x@, size@, constant, fx@);
        let fy = match_sym_id(x@, y@, d@, size@, constant, fx@);
        id_mono(fx@, fy, 2 * d@, o@);
        fy
    }
}

/// `make_resize` from `InsertDeleteDistance` to `SymmetricDistance` is stable.
#[logic(prophetic)]
#[requires(resize_contract(t, input_domain, size, constant))]
#[requires(<InsertDeleteDistance as EventModel>::close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(fx)] && t.stability_map.post()[d][Ok(o)])]
#[ensures(resized(<InsertDeleteDistance as IsMetricOrdered>::ORDERED, <SymmetricDistance as IsMetricOrdered>::ORDERED,
    y@, size@, constant, result))]
#[ensures(<SymmetricDistance as EventModel>::close(fx@, result, o@))]
pub fn resize_id_sym_stable<TA: CheckAtom>(
    t: Resize<TA, InsertDeleteDistance, SymmetricDistance>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    size: usize,
    constant: TA,
    x: Vec<TA>,
    y: Vec<TA>,
    d: IntDistance,
    fx: Vec<TA>,
    o: IntDistance,
) -> Seq<TA> {
    pearlite! {
        out_resized(<InsertDeleteDistance as IsMetricOrdered>::ORDERED, <SymmetricDistance as IsMetricOrdered>::ORDERED, x@, size@, constant, fx@);
        match_id_sym(x@, y@, d@, size@, constant, fx@)
    }
}

/// `make_resize` from `InsertDeleteDistance` to `InsertDeleteDistance` is stable.
#[logic(prophetic)]
#[requires(resize_contract(t, input_domain, size, constant))]
#[requires(<InsertDeleteDistance as EventModel>::close(x@, y@, d@))]
#[requires(t.function.post()[x][Ok(fx)] && t.stability_map.post()[d][Ok(o)])]
#[ensures(resized(<InsertDeleteDistance as IsMetricOrdered>::ORDERED, <InsertDeleteDistance as IsMetricOrdered>::ORDERED,
    y@, size@, constant, result))]
#[ensures(<InsertDeleteDistance as EventModel>::close(fx@, result, o@))]
pub fn resize_id_id_stable<TA: CheckAtom>(
    t: Resize<TA, InsertDeleteDistance, InsertDeleteDistance>,
    input_domain: VectorDomain<AtomDomain<TA>>,
    size: usize,
    constant: TA,
    x: Vec<TA>,
    y: Vec<TA>,
    d: IntDistance,
    fx: Vec<TA>,
    o: IntDistance,
) -> Seq<TA> {
    pearlite! {
        out_resized(<InsertDeleteDistance as IsMetricOrdered>::ORDERED, <InsertDeleteDistance as IsMetricOrdered>::ORDERED, x@, size@, constant, fx@);
        let fy = match_id_id(x@, y@, d@, size@, constant, fx@);
        id_mono(fx@, fy, 2 * d@, o@);
        fy
    }
}
