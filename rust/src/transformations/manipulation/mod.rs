#[cfg(feature = "ffi")]
mod ffi;

use opendp_derive::bootstrap;

use crate::core::{Domain, Function, Metric, MetricSpace, StabilityMap, Transformation};
use crate::domains::{AtomDomain, VectorDomain};
use crate::error::*;
use crate::metrics::EventLevelMetric;
#[cfg(creusot)]
use crate::metrics::IntDistance;
use crate::traits::{CheckAtom, CheckNull};
#[cfg(creusot)]
use creusot_std::{
    logic::Seq,
    macros::{ensures, invariant, logic, proof_assert, requires, snapshot, trusted},
    prelude::inv,
    std::ops::{FnExt, FnOnceExt},
};

/// A [`Domain`] representing a dataset.
///
/// This is distinguished from other domains
/// because each element in the dataset corresponds to an individual.
pub trait DatasetDomain: Domain {
    /// The domain of each element in the dataset.
    ///
    /// For vectors, this is the domain of the vector elements,
    /// for dataframes, this is the domain of the dataframe rows,
    /// and so on.
    type ElementDomain: Domain;

    /// Ghost model: the rows of a dataset.
    #[cfg(creusot)]
    #[logic]
    fn rows(value: Self::Carrier) -> Seq<<Self::ElementDomain as Domain>::Carrier>;
}

impl<D: Domain> DatasetDomain for VectorDomain<D> {
    type ElementDomain = D;

    #[cfg(creusot)]
    #[logic(open)]
    fn rows(value: Vec<D::Carrier>) -> Seq<D::Carrier> {
        pearlite! { value@ }
    }
}

pub trait RowByRowDomain<DO: DatasetDomain>: DatasetDomain {
    /// Ghost model of `translate`.
    #[cfg(creusot)]
    #[logic]
    fn translated(self, output_row_domain: DO::ElementDomain) -> DO;

    #[cfg_attr(creusot, ensures(result == self.translated(output_row_domain)))]
    fn translate(&self, output_row_domain: DO::ElementDomain) -> DO;

    /// Applies `row_function` to each row. On success, the output rows are the images of the input
    /// rows, and the result is an error only if `row_function` fails on some row.
    #[cfg_attr(creusot, requires(forall<i> 0 <= i && i < Self::rows(*value).len() ==>
        row_function.precondition((&Self::rows(*value)[i],))))]
    #[cfg_attr(creusot, ensures(forall<out: DO::Carrier> result == Ok(out) ==>
        DO::rows(out).len() == Self::rows(*value).len()
        && forall<i> 0 <= i && i < Self::rows(*value).len() ==>
            row_function.postcondition((&Self::rows(*value)[i],), Ok(DO::rows(out)[i]))))]
    #[cfg_attr(creusot, ensures((forall<i, e: Error> 0 <= i && i < Self::rows(*value).len() ==>
            !row_function.postcondition((&Self::rows(*value)[i],), Err(e)))
        ==> exists<out: DO::Carrier> result == Ok(out)))]
    fn apply_rows(
        value: &Self::Carrier,
        row_function: &impl Fn(
            &<Self::ElementDomain as Domain>::Carrier,
        ) -> Fallible<<DO::ElementDomain as Domain>::Carrier>,
    ) -> Fallible<DO::Carrier>;
}

impl<DIA: Domain, DOA: Domain> RowByRowDomain<VectorDomain<DOA>> for VectorDomain<DIA> {
    #[cfg(creusot)]
    #[logic(open)]
    fn translated(self, output_row_domain: DOA) -> VectorDomain<DOA> {
        VectorDomain {
            element_domain: output_row_domain,
            size: self.size,
        }
    }

    #[cfg_attr(creusot, ensures(result == self.translated(output_row_domain)))]
    fn translate(
        &self,
        output_row_domain: <VectorDomain<DOA> as DatasetDomain>::ElementDomain,
    ) -> VectorDomain<DOA> {
        VectorDomain {
            element_domain: output_row_domain,
            size: self.size,
        }
    }

    #[cfg_attr(creusot, requires(forall<i> 0 <= i && i < value@.len() ==>
        row_function.precondition((&value@[i],))))]
    #[cfg_attr(creusot, ensures(forall<out: Vec<DOA::Carrier>> result == Ok(out) ==>
        out@.len() == value@.len()
        && forall<i> 0 <= i && i < value@.len() ==>
            row_function.postcondition((&value@[i],), Ok(out@[i]))))]
    #[cfg_attr(creusot, ensures((forall<i, e: Error> 0 <= i && i < value@.len() ==>
            !row_function.postcondition((&value@[i],), Err(e)))
        ==> exists<out: Vec<DOA::Carrier>> result == Ok(out)))]
    fn apply_rows(
        value: &Self::Carrier,
        row_function: &impl Fn(&DIA::Carrier) -> Fallible<DOA::Carrier>,
    ) -> Fallible<Vec<DOA::Carrier>> {
        let mut out = Vec::with_capacity(value.len());
        #[cfg_attr(creusot, invariant(out@.len() == produced.len()
            && forall<j> 0 <= j && j < out@.len() ==>
                row_function.postcondition((&value@[j],), Ok(out@[j]))))]
        for i in 0..value.len() {
            match row_function(&value[i]) {
                Ok(row) => out.push(row),
                Err(e) => {
                    #[cfg(creusot)]
                    proof_assert!(row_function.postcondition((&value@[i@],), Err(e)));
                    return Err(e);
                }
            }
        }
        Ok(out)
    }
}

/// The contract of [`make_row_by_row`] on success: as [`row_by_row_contract`], for a row function
/// `f` that cannot fail. The function maps each row by `f`, and never fails.
#[cfg(creusot)]
#[logic(open, prophetic)]
pub fn row_by_row_infallible_contract<DI, DO, M, F>(
    t: Transformation<DI, M, DO, M>,
    input_domain: DI,
    output_row_domain: DO::ElementDomain,
    f: F,
) -> bool
where
    DI: RowByRowDomain<DO>,
    DO: DatasetDomain,
    M: EventLevelMetric,
    (DI, M): MetricSpace,
    (DO, M): MetricSpace,
    F: Fn(&<DI::ElementDomain as Domain>::Carrier) -> <DO::ElementDomain as Domain>::Carrier,
{
    pearlite! {
        t.input_domain == input_domain
        && t.output_domain == input_domain.translated(output_row_domain)
        && (forall<x: DI::Carrier> inv(x) && (forall<i> 0 <= i && i < DI::rows(x).len() ==>
                inv(DI::rows(x)[i]) && f.precondition((&DI::rows(x)[i],)))
            ==> t.function.pre()[x])
        && (forall<x: DI::Carrier, y: DO::Carrier> t.function.post()[x][Ok(y)] ==>
            DO::rows(y).len() == DI::rows(x).len()
            && forall<i> 0 <= i && i < DI::rows(x).len() ==>
                f.postcondition((&DI::rows(x)[i],), DO::rows(y)[i]))
        && (forall<x: DI::Carrier, r: Fallible<DO::Carrier>> t.function.post()[x][r] ==>
            exists<y: DO::Carrier> r == Ok(y))
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= d@)
    }
}

/// Constructs a [`Transformation`] representing an arbitrary row-by-row transformation.
#[cfg_attr(creusot, ensures(forall<t: Transformation<DI, M, DO, M>> result == Ok(t) ==>
    row_by_row_infallible_contract(t, input_domain, output_row_domain, row_function)))]
pub(crate) fn make_row_by_row<DI, DO, M>(
    input_domain: DI,
    input_metric: M,
    output_row_domain: DO::ElementDomain,
    row_function: impl 'static
    + Fn(
        &<DI::ElementDomain as Domain>::Carrier,
    ) -> <DO::ElementDomain as Domain>::Carrier
    + Send
    + Sync,
) -> Fallible<Transformation<DI, M, DO, M>>
where
    DI: RowByRowDomain<DO>,
    DO: DatasetDomain,
    M: EventLevelMetric,
    (DI, M): MetricSpace,
    (DO, M): MetricSpace,
{
    #[cfg(creusot)]
    let f = snapshot!(row_function);
    let wrapped = move |arg: &<DI::ElementDomain as Domain>::Carrier| Ok(row_function(arg));
    #[cfg(creusot)]
    proof_assert!(forall<a: <DI::ElementDomain as Domain>::Carrier> inv(a) && f.precondition((&a,)) ==> wrapped.precondition((&a,)));
    #[cfg(creusot)]
    proof_assert!(forall<a: <DI::ElementDomain as Domain>::Carrier, r: Fallible<<DO::ElementDomain as Domain>::Carrier>>
        wrapped.postcondition((&a,), r) ==> exists<w: <DO::ElementDomain as Domain>::Carrier> r == Ok(w) && f.postcondition((&a,), w));
    make_row_by_row_fallible(input_domain, input_metric, output_row_domain, wrapped)
}

/// The contract of [`make_row_by_row_fallible`] on success.
///
/// The output domain is the input domain with each row in `output_row_domain`. The function maps
/// each row by `f`: it is defined wherever `f` is defined on every row, its output rows are the
/// images of the input rows, and it fails only if `f` fails on some row. The stability map is at
/// least the identity.
#[cfg(creusot)]
#[logic(open, prophetic)]
pub fn row_by_row_contract<DI, DO, M, F>(
    t: Transformation<DI, M, DO, M>,
    input_domain: DI,
    output_row_domain: DO::ElementDomain,
    f: F,
) -> bool
where
    DI: RowByRowDomain<DO>,
    DO: DatasetDomain,
    M: EventLevelMetric,
    (DI, M): MetricSpace,
    (DO, M): MetricSpace,
    F: Fn(
        &<DI::ElementDomain as Domain>::Carrier,
    ) -> Fallible<<DO::ElementDomain as Domain>::Carrier>,
{
    pearlite! {
        t.input_domain == input_domain
        && t.output_domain == input_domain.translated(output_row_domain)
        && (forall<x: DI::Carrier> inv(x) && (forall<i> 0 <= i && i < DI::rows(x).len() ==>
                f.precondition((&DI::rows(x)[i],)))
            ==> t.function.pre()[x])
        && (forall<x: DI::Carrier, y: DO::Carrier> t.function.post()[x][Ok(y)] ==>
            DO::rows(y).len() == DI::rows(x).len()
            && forall<i> 0 <= i && i < DI::rows(x).len() ==>
                f.postcondition((&DI::rows(x)[i],), Ok(DO::rows(y)[i])))
        && (forall<x: DI::Carrier, r: Fallible<DO::Carrier>> t.function.post()[x][r] ==>
            (forall<i, e: Error> 0 <= i && i < DI::rows(x).len() ==>
                !f.postcondition((&DI::rows(x)[i],), Err(e)))
            ==> exists<y: DO::Carrier> r == Ok(y))
        && (forall<d: IntDistance, o: IntDistance> t.stability_map.post()[d][Ok(o)] ==> o@ >= d@)
    }
}

/// Constructs a [`Transformation`] representing an arbitrary row-by-row transformation.
#[cfg_attr(creusot, ensures(forall<t: Transformation<DI, M, DO, M>> result == Ok(t) ==>
    row_by_row_contract(t, input_domain, output_row_domain, row_function)))]
pub(crate) fn make_row_by_row_fallible<DI, DO, M>(
    input_domain: DI,
    input_metric: M,
    output_row_domain: DO::ElementDomain,
    row_function: impl 'static
    + Fn(
        &<DI::ElementDomain as Domain>::Carrier,
    ) -> Fallible<<DO::ElementDomain as Domain>::Carrier>
    + Send
    + Sync,
) -> Fallible<Transformation<DI, M, DO, M>>
where
    DI: RowByRowDomain<DO>,
    DO: DatasetDomain,
    M: EventLevelMetric,
    (DI, M): MetricSpace,
    (DO, M): MetricSpace,
{
    let output_domain = input_domain.translate(output_row_domain);
    Transformation::new(
        input_domain,
        input_metric.clone(),
        output_domain,
        input_metric,
        Function::new_fallible(move |arg: &DI::Carrier| DI::apply_rows(arg, &row_function)),
        StabilityMap::new_from_constant(1),
    )
}

#[bootstrap(
    features("contrib", "honest-but-curious"),
    generics(D(suppress), M(suppress))
)]
/// Make a Transformation representing the identity function.
///
/// WARNING: In Python, this function does not ensure that the domain and metric form a valid metric space.
/// However, if the domain and metric do not form a valid metric space,
/// then the resulting Transformation won't be chainable with any valid Transformation,
/// so it cannot be used to introduce an invalid metric space into a chain of valid Transformations.
///
/// # Arguments
/// * `domain` - Domain of input data
/// * `metric` - Metric on input domain
///
/// # Generics
/// * `D` - Domain of the identity function. Must be `VectorDomain<AtomDomain<T>>` or `AtomDomain<T>`
/// * `M` - Metric. Must be a dataset metric if D is a VectorDomain or a sensitivity metric if D is an AtomDomain
///
/// # Why honest-but-curious?
/// For the result to be a valid transformation, the `input_domain` and `input_metric` pairing must form a valid metric space.
/// For instance, the symmetric distance metric and atom domain do not form a valid metric space,
/// because the metric cannot be used to measure distances between any two elements of an atom domain.
/// Whereas, the symmetric distance metric and vector domain,
/// or absolute distance metric and atom domain on a scalar type, both form valid metric spaces.
#[cfg_attr(creusot, trusted)]
pub fn make_identity<D, M>(domain: D, metric: M) -> Fallible<Transformation<D, M, D, M>>
where
    D: Domain,
    D::Carrier: Clone,
    M: Metric,
    M::Distance: Clone,
    (D, M): MetricSpace,
{
    Transformation::new(
        domain.clone(),
        metric.clone(),
        domain,
        metric,
        Function::new(|arg: &D::Carrier| arg.clone()),
        StabilityMap::new(|d_in: &M::Distance| d_in.clone()),
    )
}

#[bootstrap(
    features("contrib"),
    arguments(
        input_domain(c_type = "AnyDomain *"),
        input_metric(c_type = "AnyMetric *")
    ),
    generics(TIA(suppress), M(suppress)),
    derived_types(
        TIA = "$get_atom(get_type(input_domain))",
        M = "$get_type(input_metric)"
    )
)]
/// Make a Transformation that checks if each element is equal to `value`.
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
/// * `value` - value to check against
///
/// # Generics
/// * `TIA` - Atomic Input Type. Type of elements in the input vector
#[cfg_attr(creusot, trusted)]
pub fn make_is_equal<TIA, M>(
    input_domain: VectorDomain<AtomDomain<TIA>>,
    input_metric: M,
    value: TIA,
) -> Fallible<Transformation<VectorDomain<AtomDomain<TIA>>, M, VectorDomain<AtomDomain<bool>>, M>>
where
    TIA: 'static + PartialEq + CheckAtom,
    M: EventLevelMetric,
    (VectorDomain<AtomDomain<TIA>>, M): MetricSpace,
    (VectorDomain<AtomDomain<bool>>, M): MetricSpace,
{
    make_row_by_row(
        input_domain,
        input_metric,
        AtomDomain::default(),
        move |v| v == &value,
    )
}

#[bootstrap(features("contrib"), generics(M(suppress), DIA(suppress)))]
/// Make a Transformation that checks if each element in a vector is null or nan.
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
///
/// # Generics
/// * `M` - Metric on input domain.
/// * `DIA` - Atomic Input Domain. Either `OptionDomain<AtomDomain<TIA>>` or `AtomDomain<TIA>`
#[cfg_attr(creusot, trusted)]
pub fn make_is_null<M, DIA>(
    input_domain: VectorDomain<DIA>,
    input_metric: M,
) -> Fallible<Transformation<VectorDomain<DIA>, M, VectorDomain<AtomDomain<bool>>, M>>
where
    DIA: Domain,
    DIA::Carrier: 'static + CheckNull,
    M: EventLevelMetric,
    (VectorDomain<DIA>, M): MetricSpace,
    (VectorDomain<AtomDomain<bool>>, M): MetricSpace,
{
    make_row_by_row(input_domain, input_metric, AtomDomain::default(), |v| {
        v.is_null()
    })
}

#[cfg(test)]
mod test;
