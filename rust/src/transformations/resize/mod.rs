#[cfg(feature = "ffi")]
mod ffi;

use opendp_derive::bootstrap;

use crate::core::{Domain, Function, Metric, MetricSpace, StabilityMap, Transformation};
use crate::domains::{AtomDomain, VectorDomain};
use crate::error::Fallible;
use crate::metrics::{InsertDeleteDistance, IntDistance, SymmetricDistance};
use crate::traits::CheckAtom;
use crate::traits::samplers::Shuffle;
use std::cmp::Ordering;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
use creusot_std::macros::{ensures, invariant, proof_assert, requires, snapshot};
#[cfg(creusot)]
pub use proof::*;

#[doc(hidden)]
pub trait IsMetricOrdered: Metric + crate::verification::MaybeEventModel {
    const ORDERED: bool;
}
impl IsMetricOrdered for SymmetricDistance {
    const ORDERED: bool = false;
}
impl IsMetricOrdered for InsertDeleteDistance {
    const ORDERED: bool = true;
}

#[bootstrap(
    features("contrib"),
    arguments(constant(rust_type = "$get_atom(get_type(input_domain))")),
    generics(TA(suppress), MI(suppress), MO(default = "SymmetricDistance"))
)]
/// Make a Transformation that either truncates or imputes records
/// with `constant` to match a provided `size`.
///
/// # Arguments
/// * `input_domain` - Domain of input data.
/// * `input_metric` - Metric of input data.
/// * `size` - Number of records in output data.
/// * `constant` - Value to impute with.
///
/// # Generics
/// * `TA` - Atomic Type.
/// * `MI` - Input Metric. One of `InsertDeleteDistance` or `SymmetricDistance`
/// * `MO` - Output Metric. One of `InsertDeleteDistance` or `SymmetricDistance`
///
/// # Returns
/// A vector of the same type `TA`, but with the provided `size`.
#[cfg_attr(creusot, ensures(forall<t: Transformation<VectorDomain<AtomDomain<TA>>, MI, VectorDomain<AtomDomain<TA>>, MO>>
    result == Ok(t) ==> resize_contract(t, input_domain, size, constant)))]
pub fn make_resize<TA, MI, MO>(
    input_domain: VectorDomain<AtomDomain<TA>>,
    input_metric: MI,
    size: usize,
    constant: TA,
) -> Fallible<Transformation<VectorDomain<AtomDomain<TA>>, MI, VectorDomain<AtomDomain<TA>>, MO>>
where
    TA: 'static + Clone + CheckAtom,
    MI: IsMetricOrdered<Distance = IntDistance>,
    MO: IsMetricOrdered<Distance = IntDistance> + Default,
    (VectorDomain<AtomDomain<TA>>, MI): MetricSpace,
    (VectorDomain<AtomDomain<TA>>, MO): MetricSpace,
{
    if !input_domain.element_domain.member(&constant)? {
        return fallible!(MakeTransformation, "constant must be a member of DA");
    }
    if size == 0 {
        return fallible!(MakeTransformation, "row size must be greater than zero");
    }

    Transformation::new(
        input_domain.clone(),
        input_metric,
        input_domain.with_size(size),
        MO::default(),
        Function::new_fallible(move |arg: &Vec<TA>| resize_vec::<TA, MI, MO>(arg, size, &constant)),
        // Consider when a dataset has zero records and is resized to length 1.
        // The resulting dataset will be `vec![constant]`
        // Now consider a neighboring dataset that differs by one addition of `value`.
        // The resulting dataset will be `vec![value]`.
        // `vec![constant]` and `vec![value]` differ by an addition and deletion, or distance 2.
        // In the worst case, for each addition in the input, there are two changes in the output
        StabilityMap::new_from_constant(2),
    )
}

/// Pads `arg` with `constant`, or truncates it, to `size` rows.
#[cfg_attr(creusot, ensures(forall<y: Vec<TA>> result == Ok(y) ==>
    resize_out(MI::ORDERED, MO::ORDERED, arg@, size@, *constant, y@)))]
fn resize_vec<TA: CheckAtom, MI: IsMetricOrdered, MO: IsMetricOrdered>(
    arg: &Vec<TA>,
    size: usize,
    constant: &TA,
) -> Fallible<Vec<TA>> {
    #[cfg(creusot)]
    proof_assert!(atom_clone::<TA>());
    Ok(match arg.len().cmp(&size) {
        Ordering::Less | Ordering::Equal => {
            let mut data = pad(arg, size, constant);
            // if output metric is ordered, then shuffle the imputed values into the data
            if MO::ORDERED {
                #[cfg(creusot)]
                let before = snapshot!(data);
                data.shuffle()?;
                #[cfg(creusot)]
                proof_assert!(before@ == padded(arg@, size@, *constant) && before.reorders(data));
            }
            data
        }
        Ordering::Greater => {
            let mut data = arg.clone();
            #[cfg(creusot)]
            proof_assert!(data@ == arg@);
            // if input metric is not ordered, then shuffle so that the slice is a random draw from the data
            if !MI::ORDERED {
                #[cfg(creusot)]
                let before = snapshot!(data);
                data.shuffle()?;
                #[cfg(creusot)]
                proof_assert!(before@ == arg@ && before.reorders(data) && shuffle_len(*before, data));
            }
            #[cfg(creusot)]
            proof_assert!(size@ < data@.len());
            let out = data[..size].to_vec();
            #[cfg(creusot)]
            proof_assert!(out@ == data@.subsequence(0, size@));
            out
        }
    })
}

/// `arg` followed by copies of `constant`, up to `size` rows.
#[cfg_attr(creusot, requires(arg@.len() <= size@))]
#[cfg_attr(creusot, ensures(result@ == arg@.concat(rep(*constant, size@ - arg@.len()))))]
fn pad<TA: CheckAtom>(arg: &Vec<TA>, size: usize, constant: &TA) -> Vec<TA> {
    #[cfg(creusot)]
    proof_assert!(atom_clone::<TA>());
    let mut data = Vec::with_capacity(size);
    #[cfg_attr(creusot, invariant(data@ == arg@.subsequence(0, produced.len())))]
    for i in 0..arg.len() {
        data.push(arg[i].clone());
    }
    #[cfg_attr(creusot, invariant(data@ == arg@.concat(rep(*constant, produced.len()))))]
    for _ in arg.len()..size {
        data.push(constant.clone());
    }
    data
}

#[cfg(test)]
mod test;
