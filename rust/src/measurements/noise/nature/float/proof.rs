//! Verification of the float discretization, `make_float_to_bigint`.
//!
//! Each value is clamped to the finite range and rounded to the nearest multiple of `2^k` (ties
//! up), and the output is the integer multiple. Finite floats are multiples of `g = 2^min_k`, so
//! rounding two of them moves their difference by less than `2^k`, hence by at most `2^k - g`
//! (`round_lipschitz`). Summed over the differing elements, the L1 distance grows by at most
//! `size (2^k - g)`, the rounding distance, and dividing by `2^k` gives the stability map.
use creusot_std::{
    logic::{Int, real::Real, such_that},
    prelude::*,
};
use dashu::{integer::IBig, rational::RBig};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    metrics::LpDistance,
    traits::{Float, Number},
    verification::{
        dashu::{pow2_pos, pow2r, pow2r_add, pow2r_lt},
        float::{float_grid, pow2},
        privacy::t_valid,
        real_abs,
    },
};

/// Ghost model of `x.clamp(MIN_FINITE, MAX_FINITE)`.
#[logic(opaque)]
pub fn fclamp<T>(_x: T) -> T {
    dead
}

/// Facts about clamping floats to the finite range, and converting them to `RBig`.
///
/// Trusted: `num::Float::clamp` returns `min` below `min`, `max` above `max`, and otherwise the value
/// itself, so it is the identity on finite values and maps the infinities to `MIN_FINITE` and
/// `MAX_FINITE`. `RBig::try_from` on `f32` and `f64` is exact on finite values and fails otherwise.
#[trusted]
#[logic(opaque)]
#[ensures(result)]
#[ensures(forall<x: T, lo: T, hi: T> <T as num::Float>::clamp.precondition((x, lo, hi)))]
#[ensures(forall<x: T, r: T>
    <T as num::Float>::clamp.postcondition((x, T::MIN_FINITE, T::MAX_FINITE), r) ==> r == fclamp(x))]
#[ensures(fclamp_facts::<T>())]
#[ensures(forall<x: T> <RBig as TryFrom<T>>::try_from.precondition((x,)))]
#[ensures(forall<x: T, r: RBig> <RBig as TryFrom<T>>::try_from.postcondition((x,), Ok(r)) ==>
    x.finite() && r.deep_model() == x.real())]
#[ensures(forall<x: T, e: <RBig as TryFrom<T>>::Error>
    <RBig as TryFrom<T>>::try_from.postcondition((x,), Err(e)) ==> !x.finite())]
pub fn float_conversion_facts<T: Float>() -> bool
where
    RBig: TryFrom<T>,
{
    dead
}

/// Clamping to the finite range is the identity on finite values, and gives a finite value on
/// non-null ones.
///
/// Trusted: as `float_conversion_facts`.
#[trusted]
#[logic(opaque)]
#[ensures(result)]
#[ensures(forall<x: T> x.finite() ==> fclamp(x) == x)]
#[ensures(forall<x: T> x.non_null() ==> fclamp(x).finite())]
pub fn fclamp_facts<T: Float>() -> bool {
    dead
}

/// Converting a number to `RBig` is exact.
///
/// Trusted: `RBig: TryFrom<Q>` is implemented by `dashu` for the primitive numbers, exactly
/// (floats fail when not finite).
#[trusted]
#[logic(opaque)]
#[ensures(result)]
#[ensures(forall<x: Q> <RBig as TryFrom<Q>>::try_from.precondition((x,)))]
#[ensures(forall<x: Q, r: RBig> <RBig as TryFrom<Q>>::try_from.postcondition((x,), Ok(r)) ==>
    r.deep_model() == x.real())]
pub fn number_conversion_facts<Q: Number>() -> bool
where
    RBig: TryFrom<Q>,
{
    dead
}

/// `n` is `x`, clamped to the finite range, rounded to the nearest multiple of `2^k` (ties up),
/// in units of `2^k`. Stated for non-null `x`.
#[logic(open)]
pub fn rounds_to<T: Float>(x: T, n: IBig, k: Int) -> bool {
    pearlite! {
        x.non_null() ==>
            Real::from_int(n.deep_model()) * Real::from_int(2) - Real::from_int(1)
                <= fclamp(x).real() * pow2r(-k) * Real::from_int(2)
            && fclamp(x).real() * pow2r(-k) * Real::from_int(2)
                < Real::from_int(n.deep_model()) * Real::from_int(2) + Real::from_int(1)
    }
}

/// The distance between two elements of float datasets: 0 if they are equal, and otherwise the
/// absolute difference of their (finite) values.
#[logic(open)]
pub fn fdist<T: Float>(a: T, b: T) -> Real {
    pearlite! { if a == b { Real::from_int(0) } else { real_abs(a.real() - b.real()) } }
}

/// The L1 distance between float datasets of equal lengths.
#[logic(open)]
#[variant(x.len())]
pub fn l1_float<T: Float>(x: Seq<T>, y: Seq<T>) -> Real {
    pearlite! {
        if x.len() == 0 { Real::from_int(0) } else {
            l1_float(x.subsequence(0, x.len() - 1), y.subsequence(0, x.len() - 1))
                + fdist(x[x.len() - 1], y[x.len() - 1])
        }
    }
}

/// Float datasets within L1 distance `d`: of equal lengths, differing only in finite elements.
#[logic(open)]
pub fn l1_close_float<T: Float>(x: Seq<T>, y: Seq<T>, d: Real) -> bool {
    pearlite! {
        x.len() == y.len()
        && (forall<i> 0 <= i && i < x.len() ==> x[i] == y[i] || (x[i].finite() && y[i].finite()))
        && l1_float(x, y) <= d
    }
}

/// Absolute value of an integer.
#[logic(open)]
pub fn iabs(v: Int) -> Int {
    pearlite! { if v >= 0 { v } else { -v } }
}

/// The L1 distance between integer datasets of equal lengths.
#[logic(open)]
#[variant(x.len())]
pub fn l1_int(x: Seq<IBig>, y: Seq<IBig>) -> Int {
    pearlite! {
        if x.len() == 0 { 0 } else {
            l1_int(x.subsequence(0, x.len() - 1), y.subsequence(0, x.len() - 1))
                + iabs(x[x.len() - 1].deep_model() - y[x.len() - 1].deep_model())
        }
    }
}

/// `x` is a member of the input domain: of the domain's size, if any, with non-null elements.
#[logic(open)]
pub fn in_float_domain<T: Float>(x: Seq<T>, size: Option<usize>) -> bool {
    pearlite! {
        (forall<i> 0 <= i && i < x.len() ==> x[i].non_null())
        && match size { Some(n) => x.len() == n@, None => true }
    }
}

pub type FloatToBigint<T, const P: usize, QI> = Transformation<
    VectorDomain<AtomDomain<T>>,
    LpDistance<P, QI>,
    VectorDomain<AtomDomain<IBig>>,
    LpDistance<P, RBig>,
>;

/// The rounding distance for `size` elements: `size (2^k - 2^min_k)`, or 0 if rounding is exact.
#[logic(open)]
pub fn rounding_distance<T: Float>(k: Int, size: Option<usize>) -> Real {
    pearlite! {
        if k == T::min_k() { Real::from_int(0) } else {
            (pow2r(k) - pow2r(T::min_k())) * Real::from_int(match size { Some(n) => n@, None => 0 })
        }
    }
}

/// The contract of `make_float_to_bigint` on success.
#[logic(open, prophetic)]
pub fn float_to_bigint_contract<T: Float, const P: usize, QI: Number>(
    t: FloatToBigint<T, P, QI>,
    input_domain: VectorDomain<AtomDomain<T>>,
    k: i32,
) -> bool {
    pearlite! {
        t.input_domain == input_domain
        && !input_domain.element_domain.has_nan()
        && t.output_domain.size == input_domain.size
        && k@ >= T::min_k()
        && (k@ == T::min_k() || input_domain.size != None)
        // the function can be evaluated on any dataset, and rounds each element
        && (forall<x: Vec<T>> inv(x) ==> t.function.pre()[x])
        && (forall<x: Vec<T>, e: crate::error::Error> !t.function.post()[x][Err(e)])
        && (forall<x: Vec<T>, y: Vec<IBig>> t.function.post()[x][Ok(y)] ==>
            y@.len() == x@.len() && forall<i> 0 <= i && i < x@.len() ==> rounds_to(x@[i], y@[i], k@))
        // the stability map: (d_in + rounding distance) / 2^k
        && (P == 1usize ==> forall<d: QI, o: RBig> inv(d) && t.stability_map.post()[d][Ok(o)] ==>
            o.deep_model() == (d.real() + rounding_distance::<T>(k@, input_domain.size)) * pow2r(-k@))
    }
}

/// Rounding moves a difference by less than one step: for integer multiples `m`, `m2` of the grid
/// `g` and `n`, `n2` of the step `p g`, `|n - n2| p <= |m - m2| + p - 1`.
#[logic]
#[requires(p >= 1)]
#[requires((2 * n - 1) * p <= 2 * m && 2 * m < (2 * n + 1) * p)]
#[requires((2 * n2 - 1) * p <= 2 * m2 && 2 * m2 < (2 * n2 + 1) * p)]
#[ensures(iabs(n - n2) * p <= iabs(m - m2) + p - 1)]
pub fn round_lipschitz(m: Int, m2: Int, n: Int, n2: Int, p: Int) {
    pearlite! {
        proof_assert!((2 * n - 1) * p == 2 * (n * p) - p && (2 * n + 1) * p == 2 * (n * p) + p);
        proof_assert!((2 * n2 - 1) * p == 2 * (n2 * p) - p && (2 * n2 + 1) * p == 2 * (n2 * p) + p);
        proof_assert!(iabs(n - n2) * p == iabs(n * p - n2 * p));
    }
}

/// `2^(g - k) 2^(k - g) = 1`, with `2^(k - g)` a positive integer, for `g <= k`.
#[logic]
#[requires(g <= k)]
#[ensures(result && pow2(k - g) >= 1 && pow2r(k - g) == Real::from_int(pow2(k - g)))]
#[ensures(Real::from_int(pow2(k - g)) * pow2r(g - k) == Real::from_int(1))]
#[ensures(pow2r(k) == Real::from_int(pow2(k - g)) * pow2r(g))]
#[ensures(pow2r(g) > Real::from_int(0) && pow2r(-k) > Real::from_int(0))]
#[ensures(pow2r(g) * pow2r(-k) == pow2r(g - k))]
pub fn grid_step(g: Int, k: Int) -> bool {
    pearlite! {
        pow2_pos(k - g);
        pow2r_add(g, k - g);
        pow2r_add(g, -k);
        pow2r_add(k, -k);
        true
    }
}

/// Rounding a finite value on the grid of multiples of `2^min_k`, in integers: with `x = m 2^min_k`
/// and `p = 2^(k - min_k)`, `(2n - 1) p <= 2m < (2n + 1) p`.
#[logic]
#[requires(x.finite() && x.non_null() && rounds_to(x, n, k) && k >= T::min_k())]
#[requires(x.real() == Real::from_int(m) * pow2r(T::min_k()))]
#[ensures(pow2(k - T::min_k()) >= 1)]
#[ensures((2 * n.deep_model() - 1) * pow2(k - T::min_k()) <= 2 * m)]
#[ensures(2 * m < (2 * n.deep_model() + 1) * pow2(k - T::min_k()))]
pub fn grid_round<T: Float>(x: T, n: IBig, k: Int, m: Int) {
    pearlite! {
        let g = T::min_k();
        let p = pow2(k - g);
        proof_assert!(grid_step(g, k));
        proof_assert!(fclamp_facts::<T>());
        proof_assert!(fclamp(x) == x);
        let t = x.real() * pow2r(-k);
        proof_assert!(t == Real::from_int(m) * pow2r(g - k));
        proof_assert!(t * Real::from_int(p) == Real::from_int(m));
        let a = Real::from_int(n.deep_model()) * Real::from_int(2) - Real::from_int(1);
        let b = Real::from_int(n.deep_model()) * Real::from_int(2) + Real::from_int(1);
        proof_assert!(a * Real::from_int(p) <= t * Real::from_int(2) * Real::from_int(p));
        proof_assert!(t * Real::from_int(2) * Real::from_int(p) < b * Real::from_int(p));
        proof_assert!(a * Real::from_int(p) == Real::from_int((2 * n.deep_model() - 1) * p));
        proof_assert!(b * Real::from_int(p) == Real::from_int((2 * n.deep_model() + 1) * p));
        proof_assert!(t * Real::from_int(2) * Real::from_int(p) == Real::from_int(2 * m));
    }
}

/// Rounding the same value gives the same integer.
#[logic]
#[requires(x.non_null() && rounds_to(x, n, k) && rounds_to(x, n2, k))]
#[ensures(n.deep_model() == n2.deep_model())]
pub fn round_unique<T: Float>(x: T, n: IBig, n2: IBig, k: Int) {}

/// A finite value is an integer multiple of `2^min_k`.
#[logic]
#[requires(x.finite())]
#[ensures(x.real() == Real::from_int(result) * pow2r(T::min_k()))]
pub fn grid_witness<T: Float>(x: T) -> Int {
    pearlite! {
        proof_assert!(float_grid::<T>());
        such_that(|m: Int| x.real() == Real::from_int(m) * pow2r(T::min_k()))
    }
}

/// `|v g| = |v| g` for `g > 0`.
#[logic]
#[requires(g > Real::from_int(0))]
#[ensures(real_abs(Real::from_int(v) * g) == Real::from_int(iabs(v)) * g)]
pub fn abs_scale(v: Int, g: Real) {}

/// `elem_bound` for differing finite elements `a = m 2^min_k`, `b = m2 2^min_k`.
#[logic]
#[requires(a.non_null() && b.non_null() && a != b && a.finite() && b.finite())]
#[requires(rounds_to(a, n, k) && rounds_to(b, n2, k) && k >= T::min_k())]
#[requires(a.real() == Real::from_int(m) * pow2r(T::min_k()))]
#[requires(b.real() == Real::from_int(m2) * pow2r(T::min_k()))]
#[ensures(Real::from_int(iabs(n.deep_model() - n2.deep_model()))
    <= (fdist(a, b) + (pow2r(k) - pow2r(T::min_k()))) * pow2r(-k))]
pub fn elem_bound_finite<T: Float>(a: T, b: T, n: IBig, n2: IBig, k: Int, m: Int, m2: Int) {
    pearlite! {
        let g = T::min_k();
        let p = pow2(k - g);
        proof_assert!(grid_step(g, k));
        grid_round(a, n, k, m);
        grid_round(b, n2, k, m2);
        round_lipschitz(m, m2, n.deep_model(), n2.deep_model(), p);
        let e = Real::from_int(iabs(n.deep_model() - n2.deep_model()));
        let q = Real::from_int(iabs(m - m2)) + Real::from_int(p) - Real::from_int(1);
        proof_assert!(a.real() - b.real() == Real::from_int(m - m2) * pow2r(g));
        abs_scale(m - m2, pow2r(g));
        proof_assert!(fdist(a, b) == Real::from_int(iabs(m - m2)) * pow2r(g));
        proof_assert!(Real::from_int(iabs(n.deep_model() - n2.deep_model()) * p) == e * Real::from_int(p));
        proof_assert!(e * Real::from_int(p) <= q);
        proof_assert!(fdist(a, b) + (pow2r(k) - pow2r(g)) == q * pow2r(g));
        proof_assert!(q * pow2r(g) * pow2r(-k) == q * pow2r(g - k));
        proof_assert!(e == e * Real::from_int(p) * pow2r(g - k));
        proof_assert!(e * Real::from_int(p) * pow2r(g - k) <= q * pow2r(g - k));
    }
}

/// The rounded elements differ by at most `(fdist + 2^k - 2^min_k) / 2^k`.
#[logic]
#[requires(a.non_null() && b.non_null() && (a == b || (a.finite() && b.finite())))]
#[requires(rounds_to(a, n, k) && rounds_to(b, n2, k) && k >= T::min_k())]
#[ensures(result)]
#[ensures(Real::from_int(iabs(n.deep_model() - n2.deep_model()))
    <= (fdist(a, b) + (pow2r(k) - pow2r(T::min_k()))) * pow2r(-k))]
pub fn elem_bound<T: Float>(a: T, b: T, n: IBig, n2: IBig, k: Int) -> bool {
    pearlite! {
        proof_assert!(step_facts(k, T::min_k()));
        if a == b {
            round_unique(a, n, n2, k);
        } else {
            elem_bound_finite(a, b, n, n2, k, grid_witness(a), grid_witness(b));
        };
        true
    }
}

/// `2^k - 2^min_k >= 0` and `2^-k > 0` for `k >= min_k`.
#[logic]
#[requires(k >= g)]
#[ensures(result && pow2r(k) - pow2r(g) >= Real::from_int(0) && pow2r(-k) > Real::from_int(0))]
#[ensures(k == g ==> pow2r(k) - pow2r(g) == Real::from_int(0))]
pub fn step_facts(k: Int, g: Int) -> bool {
    pearlite! {
        pow2r_add(k, -k);
        if k > g { pow2r_lt(g, k); };
        true
    }
}

/// Summing per-element bounds `e_i <= (dist_i + delta) s`.
#[logic]
#[requires(x.len() == y.len() && fx.len() == x.len() && fy.len() == x.len())]
#[requires(delta >= Real::from_int(0) && s > Real::from_int(0))]
#[requires(forall<i> 0 <= i && i < x.len() ==>
    Real::from_int(iabs(fx[i].deep_model() - fy[i].deep_model())) <= (fdist(x[i], y[i]) + delta) * s)]
#[ensures(Real::from_int(l1_int(fx, fy)) <= (l1_float(x, y) + Real::from_int(x.len()) * delta) * s)]
#[variant(x.len())]
pub fn sum_bound<T: Float>(
    x: Seq<T>,
    y: Seq<T>,
    fx: Seq<IBig>,
    fy: Seq<IBig>,
    delta: Real,
    s: Real,
) {
    pearlite! {
        if x.len() > 0 {
            let n = x.len() - 1;
            sum_bound(x.subsequence(0, n), y.subsequence(0, n), fx.subsequence(0, n), fy.subsequence(0, n), delta, s);
            proof_assert!(fx.subsequence(0, n).len() == n);
            proof_assert!(Real::from_int(n + 1) * delta == Real::from_int(n) * delta + delta);
        }
    }
}

/// Stability of `make_float_to_bigint` under the L1 distance: on datasets in the input domain
/// within L1 distance `d`, the integer outputs are within the stability map at `d`.
#[logic(prophetic)]
#[requires(P == 1usize)]
#[requires(float_to_bigint_contract::<T, P, QI>(t, input_domain, k))]
#[requires(in_float_domain(x@, input_domain.size) && in_float_domain(y@, input_domain.size))]
#[requires(l1_close_float(x@, y@, d.real()))]
#[requires(t.function.post()[x][Ok(fx)] && t.function.post()[y][Ok(fy)])]
#[requires(inv(d) && t.stability_map.post()[d][Ok(o)])]
#[ensures(result)]
#[ensures(fx@.len() == fy@.len())]
#[ensures(Real::from_int(l1_int(fx@, fy@)) <= o.deep_model())]
pub fn float_to_bigint_is_stable<T: Float, const P: usize, QI: Number>(
    t: FloatToBigint<T, P, QI>,
    input_domain: VectorDomain<AtomDomain<T>>,
    k: i32,
    x: Vec<T>,
    y: Vec<T>,
    d: QI,
    fx: Vec<IBig>,
    fy: Vec<IBig>,
    o: RBig,
) -> bool {
    pearlite! {
        let g = T::min_k();
        let delta = pow2r(k@) - pow2r(g);
        let s = pow2r(-k@);
        proof_assert!(step_facts(k@, g));
        proof_assert!(forall<i> 0 <= i && i < x@.len() ==> elem_bound(x@[i], y@[i], fx@[i], fy@[i], k@));
        sum_bound(x@, y@, fx@, fy@, delta, s);
        // the bound is at most (d + rounding distance) / 2^k
        proof_assert!(k@ != g ==> Real::from_int(x@.len()) * delta == rounding_distance::<T>(k@, input_domain.size));
        proof_assert!(l1_float(x@, y@) + Real::from_int(x@.len()) * delta
            <= d.real() + rounding_distance::<T>(k@, input_domain.size));
        true
    }
}

/// `t` is stable under the L1 distance: the conclusion of `float_to_bigint_is_stable`, for all
/// inputs.
#[logic(open, prophetic)]
pub fn float_to_bigint_stable<T: Float, const P: usize, QI: Number>(
    t: FloatToBigint<T, P, QI>,
    input_domain: VectorDomain<AtomDomain<T>>,
) -> bool {
    pearlite! {
        forall<x: Vec<T>, y: Vec<T>, d: QI, fx: Vec<IBig>, fy: Vec<IBig>, o: RBig>
            in_float_domain(x@, input_domain.size) && in_float_domain(y@, input_domain.size)
            && l1_close_float(x@, y@, d.real())
            && t.function.post()[x][Ok(fx)] && t.function.post()[y][Ok(fy)]
            && inv(d) && t.stability_map.post()[d][Ok(o)]
            ==> fx@.len() == fy@.len() && Real::from_int(l1_int(fx@, fy@)) <= o.deep_model()
    }
}

/// A transformation from non-null float vectors to integer vectors, under the L1 distance, that
/// can be evaluated on (and succeeds on) every dataset, preserves lengths, and is stable as in
/// `float_to_bigint_stable`, is valid.
///
/// Trusted: the definition of a valid transformation, with the L1 distance between float vectors
/// read as `l1_close_float` (equal lengths; elements that differ are finite, and their absolute
/// differences sum to at most `d`) and between integer vectors as `l1_int`. Members of the input
/// domain have non-null elements and the domain's size; every integer vector of that size is a
/// member of the output domain.
#[trusted]
#[logic(opaque)]
#[requires(P == 1usize)]
#[requires(t.input_domain == input_domain && !input_domain.element_domain.has_nan())]
#[requires(t.output_domain.size == input_domain.size)]
#[requires(forall<x: Vec<T>> inv(x) ==> t.function.pre()[x])]
#[requires(forall<x: Vec<T>, e: crate::error::Error> !t.function.post()[x][Err(e)])]
#[requires(forall<x: Vec<T>, y: Vec<IBig>> t.function.post()[x][Ok(y)] ==> y@.len() == x@.len())]
#[requires(float_to_bigint_stable(t, input_domain))]
#[ensures(result && t_valid(t))]
pub fn float_to_bigint_valid<T: Float, const P: usize, QI: Number>(
    t: FloatToBigint<T, P, QI>,
    input_domain: VectorDomain<AtomDomain<T>>,
) -> bool {
    dead
}

/// `make_float_to_bigint` (with `P = 1`) returns a valid transformation.
#[logic(prophetic)]
#[requires(P == 1usize)]
#[requires(float_to_bigint_contract::<T, P, QI>(t, input_domain, k))]
#[ensures(result && t_valid(t))]
pub fn float_to_bigint_is_valid<T: Float, const P: usize, QI: Number>(
    t: FloatToBigint<T, P, QI>,
    input_domain: VectorDomain<AtomDomain<T>>,
    k: i32,
) -> bool {
    pearlite! {
        proof_assert!(forall<x: Vec<T>, y: Vec<T>, d: QI, fx: Vec<IBig>, fy: Vec<IBig>, o: RBig>
            in_float_domain(x@, input_domain.size) && in_float_domain(y@, input_domain.size)
            && l1_close_float(x@, y@, d.real())
            && t.function.post()[x][Ok(fx)] && t.function.post()[y][Ok(fy)]
            && inv(d) && t.stability_map.post()[d][Ok(o)]
            ==> float_to_bigint_is_stable(t, input_domain, k, x, y, d, fx, fy, o));
        float_to_bigint_valid(t, input_domain)
    }
}
