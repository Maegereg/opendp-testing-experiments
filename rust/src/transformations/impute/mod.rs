#[cfg(feature = "ffi")]
mod ffi;

use opendp_derive::bootstrap;

use crate::core::{Domain, Function, MetricSpace, StabilityMap, Transformation};
use crate::domains::{AtomDomain, OptionDomain, VectorDomain};
use crate::error::Fallible;
use crate::metrics::EventLevelMetric;
use crate::traits::samplers::GeneratorOpenDP;
use crate::traits::{CheckAtom, CheckNull, Float, HasNull};
use crate::transformations::make_row_by_row;
use rand::distributions::{Distribution, Uniform, uniform::SampleUniform};

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
use crate::verification::{RealModel, float::FloatModel};
#[cfg(creusot)]
use creusot_std::macros::{ensures, requires, trusted};
#[cfg(creusot)]
pub use proof::*;

#[bootstrap(
    features("contrib"),
    generics(M(suppress), TA(suppress)),
    derived_types(TA = "$get_atom(get_type(input_domain))")
)]
/// Make a Transformation that replaces NaN values in `Vec<TA>` with uniformly distributed floats within `bounds`.
///
/// # Arguments
/// * `input_domain` - Domain of the input.
/// * `input_metric` - Metric of the input.
/// * `bounds` - Tuple of inclusive lower and upper bounds.
///
/// # Generics
/// * `M` - Metric Type. A dataset metric.
/// * `TA` - Atomic Type of data being imputed. One of `f32` or `f64`
#[cfg_attr(creusot, ensures(forall<t: Transformation<VectorDomain<AtomDomain<TA>>, M, VectorDomain<AtomDomain<TA>>, M>>
    result == Ok(t) ==> impute_uniform_contract(t, input_domain, bounds)))]
pub fn make_impute_uniform_float<M, TA>(
    input_domain: VectorDomain<AtomDomain<TA>>,
    input_metric: M,
    bounds: (TA, TA),
) -> Fallible<Transformation<VectorDomain<AtomDomain<TA>>, M, VectorDomain<AtomDomain<TA>>, M>>
where
    TA: Float + SampleUniform,
    M: EventLevelMetric,
    (VectorDomain<AtomDomain<TA>>, M): MetricSpace,
{
    let (lower, upper) = bounds;
    if is_nan(&lower) {
        return fallible!(MakeTransformation, "lower may not be nan");
    }
    if is_nan(&upper) {
        return fallible!(MakeTransformation, "upper may not be nan");
    }
    if !is_finite(&lower) || !is_finite(&upper) {
        return fallible!(MakeTransformation, "bounds must be finite");
    }
    // `lower >= upper`, as neither is NaN
    if !lt(lower, upper) {
        return fallible!(MakeTransformation, "lower must be smaller than upper");
    }

    #[cfg(creusot)]
    creusot_std::macros::proof_assert!(finite_non_null::<TA>());
    make_row_by_row(
        input_domain,
        input_metric,
        AtomDomain::new_non_nan(),
        move |v: &TA| impute_row(v, lower, upper),
    )
}

/// Replaces a null (NaN) row with a sample from `[lower, upper)`.
#[cfg_attr(creusot, requires(lower.finite() && upper.finite() && lower.real() < upper.real()))]
#[cfg_attr(creusot, ensures(imputed(*v, result, lower, upper)))]
fn impute_row<TA: Float + SampleUniform>(v: &TA, lower: TA, upper: TA) -> TA {
    if is_nan(v) {
        sample_uniform(lower, upper)
    } else {
        *v
    }
}

/// A sample from the uniform distribution on `[lower, upper)`, or `lower` if the system lacks
/// entropy.
// Trusted: `Uniform::new` panics unless `lower < upper` and both are finite, and then samples
// `lower + u * scale` with `scale` chosen so that every sample is below `upper`.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, requires(lower.finite() && upper.finite() && lower.real() < upper.real()))]
#[cfg_attr(creusot, ensures(result.finite() && lower.real() <= result.real() && result.real() < upper.real()))]
fn sample_uniform<TA: Float + SampleUniform>(lower: TA, upper: TA) -> TA {
    let mut rng = GeneratorOpenDP::new();
    let sample = Uniform::from(lower..upper).sample(&mut rng);
    rng.error.map(|_| sample).unwrap_or(lower)
}

/// `v` is NaN, which for floats is `CheckNull::is_null`.
// Trusted: `non_null` is the ghost model of non-NaN floats.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result == !v.non_null()))]
fn is_nan<TA: Float>(v: &TA) -> bool {
    v.is_null()
}

/// `v` is finite.
// Trusted: `finite` is the ghost model of finite floats.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result == v.finite()))]
fn is_finite<TA: Float>(v: &TA) -> bool {
    v.is_finite()
}

/// `a < b`.
// Trusted: IEEE `<` on finite values is `<` on the reals.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(a.finite() && b.finite() ==> result == (a.real() < b.real())))]
fn lt<TA: Float>(a: TA, b: TA) -> bool {
    a < b
}

/// Utility trait to impute with a constant, regardless of the representation of nullity.
pub trait ImputeConstantDomain: Domain {
    /// This is the type of `Self::Carrier` after imputation.
    ///
    /// On any type `D` for which the `ImputeConstantDomain` trait is implemented,
    /// the syntax `D::Imputed` refers to this associated type.
    /// For example, consider `D` to be `OptionDomain<T>`, the domain of all `Option<T>`.
    /// The implementation of this trait for `OptionDomain<T>` designates that `type Imputed = T`.
    /// Thus `OptionDomain<T>::Imputed` is `T`.
    ///
    /// # Proof Definition
    /// `Self::Imputed` can represent the set of possible output values after imputation.
    type Imputed;

    /// A function that replaces a potentially-null carrier type with a non-null imputed type.
    ///
    /// # Proof Definition
    /// For any setting of the input parameters, where `constant` is non-null,
    /// the function returns a non-null value.
    fn impute_constant<'a>(
        default: &'a Self::Carrier,
        constant: &'a Self::Imputed,
    ) -> &'a Self::Imputed;
}
// how to impute, when null represented as `Option<T>`
impl<T: CheckAtom> ImputeConstantDomain for OptionDomain<AtomDomain<T>> {
    type Imputed = T;
    #[cfg_attr(creusot, trusted)]
    fn impute_constant<'a>(
        default: &'a Self::Carrier,
        constant: &'a Self::Imputed,
    ) -> &'a Self::Imputed {
        default.as_ref().unwrap_or(constant)
    }
}
// how to impute, when null represented as T with internal nullity
impl<T: CheckAtom + HasNull> ImputeConstantDomain for AtomDomain<T> {
    type Imputed = Self::Carrier;
    #[cfg_attr(creusot, trusted)]
    fn impute_constant<'a>(
        default: &'a Self::Carrier,
        constant: &'a Self::Imputed,
    ) -> &'a Self::Imputed {
        if default.is_null() { constant } else { default }
    }
}

#[cfg_attr(creusot, trusted)]
#[bootstrap(
    features("contrib"),
    arguments(constant(
        rust_type = "$get_atom(get_type(input_domain))",
        c_type = "AnyObject *"
    )),
    generics(DIA(suppress), M(suppress))
)]
/// Make a Transformation that replaces null/None data with `constant`.
///
/// If chaining after a `make_cast`, the input type is `Option<Vec<TA>>`.
/// If chaining after a `make_cast_inherent`, the input type is `Vec<TA>`, where `TA` may take on float NaNs.
///
/// | input_domain                                    |  Input Data Type  |
/// | ----------------------------------------------- | ----------------- |
/// | `vector_domain(option_domain(atom_domain(TA)))` | `Vec<Option<TA>>` |
/// | `vector_domain(atom_domain(TA))`                | `Vec<TA>`         |
///
/// # Arguments
/// * `input_domain` - Domain of the input data. See table above.
/// * `input_metric` - Metric of the input data. A dataset metric.
/// * `constant` - Value to replace nulls with.
///
/// # Generics
/// * `DIA` - Atomic Input Domain of data being imputed.
/// * `M` - Dataset Metric.
pub fn make_impute_constant<DIA, M>(
    input_domain: VectorDomain<DIA>,
    input_metric: M,
    constant: DIA::Imputed,
) -> Fallible<Transformation<VectorDomain<DIA>, M, VectorDomain<AtomDomain<DIA::Imputed>>, M>>
where
    DIA: ImputeConstantDomain + Default,
    DIA::Imputed: 'static + Clone + CheckAtom,
    DIA::Carrier: 'static,
    M: EventLevelMetric,
    (VectorDomain<DIA>, M): MetricSpace,
    (VectorDomain<AtomDomain<DIA::Imputed>>, M): MetricSpace,
{
    let output_atom_domain = AtomDomain::new_non_nan();
    if !output_atom_domain.member(&constant)? {
        return fallible!(MakeTransformation, "Constant may not be null.");
    }

    make_row_by_row(input_domain, input_metric, output_atom_domain, move |v| {
        DIA::impute_constant(v, &constant).clone()
    })
}

/// Utility trait to drop null values from a dataset, regardless of the representation of nullity.
pub trait DropNullDomain: Domain {
    /// This is the type of `Self::Carrier` after dropping null.
    ///
    /// On any type `D` for which the `DropNullDomain` trait is implemented,
    /// the syntax `D::Imputed` refers to this associated type.
    /// For example, consider `D` to be `OptionDomain<T>`, the domain of all `Option<T>`.
    /// The implementation of this trait for `DropNullDomain<T>` designates that `type Imputed = T`.
    /// Thus `DropNullDomain<T>::Imputed` is `T`.
    type Imputed;

    /// Standardizes `D::Carrier` into an `Option<D::Imputed>`, where `D::Imputed` is never null.
    ///
    /// `Self::Imputed` may have the capacity to represent null (like `f64`),
    /// but implementations of this function must guarantee that `Self::Imputed` is never null.
    fn option(value: &Self::Carrier) -> Option<Self::Imputed>;
}

/// how to standardize into an option, when null represented as `Option<T>`
impl<T: CheckAtom + Clone> DropNullDomain for OptionDomain<AtomDomain<T>> {
    type Imputed = T;
    #[cfg_attr(creusot, trusted)]
    fn option(value: &Self::Carrier) -> Option<T> {
        if value.is_null() { None } else { value.clone() }
    }
}
/// how to standardize into an option, when null represented as T with internal nullity
impl<T: CheckAtom + HasNull + Clone> DropNullDomain for AtomDomain<T> {
    type Imputed = T;
    #[cfg_attr(creusot, trusted)]
    fn option(value: &Self::Carrier) -> Option<T> {
        if value.is_null() {
            None
        } else {
            Some(value.clone())
        }
    }
}

#[cfg_attr(creusot, trusted)]
#[bootstrap(features("contrib"), generics(DIA(suppress), M(suppress)))]
/// Make a Transformation that drops null values.
///
///
/// | input_domain                                    |
/// | ----------------------------------------------- |
/// | `vector_domain(option_domain(atom_domain(TA)))` |
/// | `vector_domain(atom_domain(TA))`                |
///
/// # Arguments
/// * `input_domain` - Domain of input data
/// * `input_metric` - Metric on input domain
///
/// # Generics
/// * `M` - Dataset Metric.
/// * `DIA` - atomic domain of input data that contains nulls.
pub fn make_drop_null<M, DIA>(
    input_domain: VectorDomain<DIA>,
    input_metric: M,
) -> Fallible<Transformation<VectorDomain<DIA>, M, VectorDomain<AtomDomain<DIA::Imputed>>, M>>
where
    DIA: DropNullDomain + Default,
    DIA::Imputed: CheckAtom,
    M: EventLevelMetric,
    (VectorDomain<DIA>, M): MetricSpace,
    (VectorDomain<AtomDomain<DIA::Imputed>>, M): MetricSpace,
{
    Transformation::new(
        input_domain,
        input_metric.clone(),
        VectorDomain::new(AtomDomain::new_non_nan()),
        input_metric,
        Function::new(|arg: &Vec<DIA::Carrier>| arg.iter().filter_map(DIA::option).collect()),
        StabilityMap::new_from_constant(1),
    )
}

#[cfg(test)]
mod test;
