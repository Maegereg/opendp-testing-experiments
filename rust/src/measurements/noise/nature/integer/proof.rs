//! Verification of the integer conversion, `make_int_to_bigint`.
//!
//! Each element is converted exactly to `IBig`, and the distance exactly to `RBig`, so the
//! transformation preserves the L_p distance between datasets.
use creusot_std::prelude::*;
use dashu::{integer::IBig, rational::RBig};

use crate::{
    core::Transformation,
    domains::{AtomDomain, VectorDomain},
    error::Error,
    metrics::LpDistance,
    traits::{Integer, Number},
    verification::privacy::t_valid,
};

pub type IntToBigint<T, const P: usize, QI> = Transformation<
    VectorDomain<AtomDomain<T>>,
    LpDistance<P, QI>,
    VectorDomain<AtomDomain<IBig>>,
    LpDistance<P, RBig>,
>;

/// Converting an integer to `IBig` is exact.
///
/// Trusted: `IBig: From<T>` is implemented by `dashu` for the primitive integers, exactly.
#[trusted]
#[logic(opaque)]
#[ensures(result)]
#[ensures(forall<x: T> <IBig as From<T>>::from.precondition((x,)))]
#[ensures(forall<x: T, r: IBig> <IBig as From<T>>::from.postcondition((x,), r) ==>
    r.deep_model() == x.deep_model())]
pub fn ibig_from_facts<T: Integer>() -> bool
where
    IBig: From<T>,
{
    dead
}

/// A transformation that converts each element of an integer vector exactly, preserving sizes,
/// and whose stability map converts the distance exactly, is valid under the `L_p` distance.
///
/// Trusted: the definition of a valid transformation; the `L_p` distance between integer vectors
/// depends only on the values of their elements, and every vector of `IBig` of the right size is
/// a member of the output domain.
#[trusted]
#[logic(opaque)]
#[requires(t.output_domain.size == t.input_domain.size)]
#[requires(forall<x: Vec<T>> inv(x) ==> t.function.pre()[x])]
#[requires(forall<x: Vec<T>, e: Error> !t.function.post()[x][Err(e)])]
#[requires(forall<x: Vec<T>, y: Vec<IBig>> t.function.post()[x][Ok(y)] ==>
    y@.len() == x@.len() && forall<i> 0 <= i && i < x@.len() ==> y@[i].deep_model() == x@[i].deep_model())]
#[requires(forall<d: QI, o: RBig> inv(d) && t.stability_map.post()[d][Ok(o)] ==>
    o.deep_model() == d.real())]
#[ensures(result && t_valid(t))]
pub fn int_to_bigint_valid<T: Integer, const P: usize, QI: Number>(
    t: IntToBigint<T, P, QI>,
) -> bool {
    dead
}
