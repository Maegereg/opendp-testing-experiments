use opendp_derive::bootstrap;

use crate::{
    core::{Domain, Function, MetricSpace, StabilityMap, Transformation},
    error::Fallible,
    metrics::IntDistance,
    traits::{IsSizedDomain, samplers::Shuffle},
};

use self::traits::{BoundedMetric, OrderedMetric, UnboundedMetric, UnorderedMetric};
#[cfg(creusot)]
use crate::core::Metric;
#[cfg(creusot)]
use creusot_std::prelude::*;

#[cfg(feature = "ffi")]
mod ffi;
pub(crate) mod traits;

/// The contract of `make_ordered_random` on success.
#[cfg(creusot)]
#[logic(open, prophetic)]
pub fn ordered_random_contract<D, MI, MO>(t: Transformation<D, MI, D, MO>) -> bool
where
    D: Domain,
    D::Carrier: Clone + Shuffle,
    MI: Metric<Distance = IntDistance>,
    MO: Metric<Distance = IntDistance>,
{
    pearlite! {
        // the function can be evaluated on any dataset,
        (forall<x: D::Carrier> inv(x) ==> t.function.pre()[x])
        // and returns a copy of it, in some order
        && (forall<x: D::Carrier, y: D::Carrier> t.function.post()[x][Ok(y)] ==>
            inv(y) && exists<c: D::Carrier> <D::Carrier as Clone>::clone.postcondition((&x,), c) && c.reorders(y))
        // the stability map returns at least d_in
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= d@)
    }
}

/// The contract of `make_unordered` on success.
#[cfg(creusot)]
#[logic(open, prophetic)]
pub fn unordered_contract<D, MI, MO>(t: Transformation<D, MI, D, MO>) -> bool
where
    D: Domain,
    D::Carrier: Clone,
    MI: Metric<Distance = IntDistance>,
    MO: Metric<Distance = IntDistance>,
{
    pearlite! {
        // the function can be evaluated on any dataset,
        (forall<x: D::Carrier> inv(x) ==> t.function.pre()[x])
        // and returns a copy of it
        && (forall<x: D::Carrier, r: Fallible<D::Carrier>> t.function.post()[x][r] ==>
            exists<y: D::Carrier> r == Ok(y) && inv(y) && <D::Carrier as Clone>::clone.postcondition((&x,), y))
        // the stability map returns at least d_in
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= d@)
    }
}

#[bootstrap(features("contrib"), generics(D(suppress), MI(suppress)))]
/// Make a Transformation that converts the unordered dataset metric `SymmetricDistance`
/// to the respective ordered dataset metric `InsertDeleteDistance` by assigning a random permutation.
///
/// | `MI`              | `MI::OrderedMetric`  |
/// | ----------------- | -------------------- |
/// | SymmetricDistance | InsertDeleteDistance |
/// | ChangeOneDistance | HammingDistance      |
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
///
/// # Generics
/// * `D` - Domain
/// * `MI` - Input Metric
#[cfg_attr(creusot, ensures(forall<t: Transformation<D, MI, D, MI::OrderedMetric>> result == Ok(t) ==>
    ordered_random_contract(t)))]
pub fn make_ordered_random<D, MI>(
    input_domain: D,
    input_metric: MI,
) -> Fallible<Transformation<D, MI, D, MI::OrderedMetric>>
where
    D: Domain,
    D::Carrier: Clone + Shuffle,
    MI: UnorderedMetric<Distance = IntDistance>,
    (D, MI): MetricSpace,
    (D, MI::OrderedMetric): MetricSpace,
{
    Transformation::new(
        input_domain.clone(),
        input_metric,
        input_domain,
        MI::OrderedMetric::default(),
        Function::new_fallible(|arg: &D::Carrier| {
            let mut data = arg.clone();
            data.shuffle()?;
            Ok(data)
        }),
        StabilityMap::new_from_constant(1),
    )
}

#[bootstrap(features("contrib"), generics(D(suppress), MI(suppress)))]
/// Make a Transformation that converts the ordered dataset metric `MI`
/// to the respective ordered dataset metric with a no-op.
///
/// | `MI`                 | `MI::UnorderedMetric` |
/// | -------------------- | --------------------- |
/// | InsertDeleteDistance | SymmetricDistance     |
/// | HammingDistance      | ChangeOneDistance     |
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
///
/// # Generics
/// * `D` - Domain
/// * `MI` - Input Metric
#[cfg_attr(creusot, ensures(forall<t: Transformation<D, MI, D, MI::UnorderedMetric>> result == Ok(t) ==>
    unordered_contract(t)))]
pub fn make_unordered<D, MI>(
    input_domain: D,
    input_metric: MI,
) -> Fallible<Transformation<D, MI, D, MI::UnorderedMetric>>
where
    D: Domain,
    D::Carrier: Clone,
    MI: OrderedMetric<Distance = IntDistance>,
    (D, MI): MetricSpace,
    (D, MI::UnorderedMetric): MetricSpace,
{
    Transformation::new(
        input_domain.clone(),
        input_metric,
        input_domain,
        MI::UnorderedMetric::default(),
        Function::new(|val: &D::Carrier| val.clone()),
        StabilityMap::new_from_constant(1),
    )
}

#[bootstrap(features("contrib"), generics(D(suppress), MI(suppress)))]
/// Make a Transformation that converts the bounded dataset metric `MI`
/// to the respective unbounded dataset metric with a no-op.
///
/// | `MI`              | `MI::UnboundedMetric` |
/// | ----------------- | --------------------- |
/// | ChangeOneDistance | SymmetricDistance     |
/// | HammingDistance   | InsertDeleteDistance  |
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
/// * `size` - Number of records in input data.
///
/// # Generics
/// * `D` - Domain. The function is a no-op so input and output domains are the same.
/// * `MI` - Input Metric.
#[cfg_attr(creusot, creusot_std::macros::trusted)]
pub fn make_metric_unbounded<D, MI>(
    input_domain: D,
    input_metric: MI,
) -> Fallible<Transformation<D, MI, D, MI::UnboundedMetric>>
where
    D: IsSizedDomain,
    D::Carrier: Clone,
    MI: BoundedMetric<Distance = IntDistance>,
    (D, MI): MetricSpace,
    (D, MI::UnboundedMetric): MetricSpace,
{
    input_domain.get_size()?;
    Transformation::new(
        input_domain.clone(),
        input_metric.clone(),
        input_domain,
        input_metric.to_unbounded(),
        Function::new(|arg: &D::Carrier| arg.clone()),
        StabilityMap::new(|d_in| d_in * 2),
    )
}

#[bootstrap(
    features("contrib"),
    arguments(domain(c_type = "AnyDomain *")),
    generics(D(suppress), MI(suppress))
)]
/// Make a Transformation that converts the unbounded dataset metric `MI`
/// to the respective bounded dataset metric with a no-op.
///
/// The constructor enforces that the input domain has known size,
/// because it must have known size to be valid under a bounded dataset metric.
///
/// | `MI`                 | `MI::BoundedMetric` |
/// | -------------------- | ------------------- |
/// | SymmetricDistance    | ChangeOneDistance   |
/// | InsertDeleteDistance | HammingDistance     |
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
/// * `size` - Number of records in input data.
///
/// # Generics
/// * `D` - Domain
/// * `MI` - Input Metric
#[cfg_attr(creusot, creusot_std::macros::trusted)]
pub fn make_metric_bounded<D, MI>(
    input_domain: D,
    input_metric: MI,
) -> Fallible<Transformation<D, MI, D, MI::BoundedMetric>>
where
    D: IsSizedDomain,
    D::Carrier: Clone,
    MI: UnboundedMetric<Distance = IntDistance>,
    (D, MI): MetricSpace,
    (D, MI::BoundedMetric): MetricSpace,
{
    input_domain.get_size()?;
    Transformation::new(
        input_domain.clone(),
        input_metric.clone(),
        input_domain,
        input_metric.to_bounded(),
        Function::new(|arg: &D::Carrier| arg.clone()),
        StabilityMap::new(|d_in| d_in / 2),
    )
}

#[cfg(test)]
mod test;
