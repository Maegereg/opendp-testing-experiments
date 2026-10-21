#[cfg(feature = "ffi")]
mod ffi;

use opendp_derive::bootstrap;

use crate::core::{MetricSpace, Transformation};
use crate::domains::{AtomDomain, VectorDomain};
use crate::error::Fallible;
use crate::metrics::EventLevelMetric;
use crate::traits::{CheckAtom, ProductOrd};
use crate::transformations::make_row_by_row_fallible;
#[cfg(creusot)]
use creusot_std::macros::{ensures, proof_assert, snapshot};

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

#[bootstrap(
    features("contrib"),
    arguments(
        input_domain(c_type = "AnyDomain *", hint = "Domain"),
        input_metric(c_type = "AnyMetric *", hint = "Metric", rust_type = b"null")
    ),
    generics(TA(suppress), M(suppress)),
    derived_types(TA = "$get_atom(get_type(input_domain))")
)]
/// Make a Transformation that clamps numeric data in `Vec<TA>` to `bounds`.
///
/// If datum is less than lower, let datum be lower.
/// If datum is greater than upper, let datum be upper.
///
/// # Arguments
/// * `input_domain` - Domain of input data.
/// * `input_metric` - Metric on input domain.
/// * `bounds` - Tuple of inclusive lower and upper bounds.
///
/// # Generics
/// * `TA` - Atomic Type
#[cfg_attr(creusot, ensures(forall<t: Clamp<TA, M>> result == Ok(t) ==>
    clamp_contract(t, input_domain, bounds)))]
pub fn make_clamp<TA: 'static + Clone + ProductOrd + PartialOrd + CheckAtom, M: EventLevelMetric>(
    input_domain: VectorDomain<AtomDomain<TA>>,
    input_metric: M,
    bounds: (TA, TA),
) -> Fallible<Transformation<VectorDomain<AtomDomain<TA>>, M, VectorDomain<AtomDomain<TA>>, M>>
where
    (VectorDomain<AtomDomain<TA>>, M): MetricSpace,
{
    input_domain.element_domain.assert_non_nan()?;

    #[cfg(creusot)]
    let bnd = snapshot!(bounds);
    let (lower, upper) = bounds;
    let output_row_domain = AtomDomain::new_closed((lower.clone(), upper.clone()))?;

    // `new_closed` compares the bounds with `PartialOrd`.
    // For pairs, `ProductOrd` is the componentwise order, which may not order the bounds.
    if lower.total_gt(&upper)? {
        return fallible!(
            MakeTransformation,
            "lower bound may not be greater than upper bound"
        );
    }

    #[cfg(creusot)]
    proof_assert!(ord_clone::<TA>());
    let result = make_row_by_row_fallible(
        input_domain,
        input_metric,
        output_row_domain,
        move |arg: &TA| arg.clone().total_clamp(lower.clone(), upper.clone()),
    );
    // The clamped rows are the image of the input rows under `clamper`.
    #[cfg(creusot)]
    proof_assert!(forall<t: Clamp<TA, M>> result == Ok(t) ==>
        forall<x: Vec<TA>, y: Vec<TA>> t.function.post()[x][Ok(y)] ==>
            y@ == x@.map(clamper(bnd.0, bnd.1)));
    result
}

#[cfg(all(test, feature = "partials"))]
mod test;
