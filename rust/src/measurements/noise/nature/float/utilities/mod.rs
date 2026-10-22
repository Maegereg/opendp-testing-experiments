use dashu::{
    base::Sign,
    integer::{IBig, UBig},
    rational::RBig,
};
use opendp_derive::proven;

#[cfg(test)]
mod test;

#[cfg(creusot)]
use crate::verification::{
    RealModel,
    dashu::{dashu_facts, pow2r, pow2r_lt, pow2r_scale},
    float::{FloatModel, float_grid},
};
use crate::{
    error::Fallible,
    traits::{ExactIntCast, Float, InfCast, InfSqrt},
};
#[cfg(creusot)]
use creusot_std::{logic::real::Real, prelude::*};

#[proven(proof_path = "measurements/noise/nature/float/utilities/find_nearest_multiple_of_2k.tex")]
/// Find index of the nearest multiple of $2^k$ from x.
///
/// # Proof Definition
/// $k$ must not be `i32::MIN`.
///
/// Return the integer $\max \mathrm{argmin}_i |i 2^k - x|$.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(Real::from_int(result.deep_model()) * Real::from_int(2) - Real::from_int(1)
    <= x.deep_model() * pow2r(-k@) * Real::from_int(2)))]
#[cfg_attr(creusot, ensures(x.deep_model() * pow2r(-k@) * Real::from_int(2)
    < Real::from_int(result.deep_model()) * Real::from_int(2) + Real::from_int(1)))]
pub fn find_nearest_multiple_of_2k(x: RBig, k: i32) -> IBig {
    // exactly compute x/2^k and break into fractional parts
    let (num, den) = x_mul_2k(x, -k).into_parts();
    (floor_div(num << 1, den) + 1) >> 1usize
}

#[proven(proof_path = "measurements/noise/nature/float/utilities/floor_div.tex")]
/// This method exists because, for negative dashu int `x` and positive dashu int `y`,
/// the result of $x / y$ is rounded towards zero.
///
/// # Proof Definition
/// Return `floor(a / b)`, where $/$ denotes real division.
#[cfg_attr(creusot, requires(b.deep_model() > 0))]
#[cfg_attr(creusot, ensures(result.deep_model() * b.deep_model() <= a.deep_model()))]
#[cfg_attr(creusot, ensures(a.deep_model() < (result.deep_model() + 1) * b.deep_model()))]
fn floor_div(a: IBig, b: UBig) -> IBig {
    if Sign::Positive == a.sign() {
        a / b
    } else {
        (a - &b + 1) / b
    }
}

#[proven(proof_path = "measurements/noise/nature/float/utilities/get_min_k.tex")]
/// # Proof Definition
/// Return the `k` where $2^k$ is the smallest distance between adjacent non-equal values in `T`.
///
/// (Adjacent non-equal values are subnormal neighbors.)
// Trusted: constant arithmetic on `T`'s associated constants, which generic code cannot see.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, ensures(result@ == T::min_k()))]
pub(crate) fn get_min_k<T: Float>() -> i32
where
    i32: ExactIntCast<T::Bits>,
{
    -i32::exact_int_cast(T::EXPONENT_BIAS).unwrap() - i32::exact_int_cast(T::MANTISSA_BITS).unwrap()
        + 1
}

#[proven(proof_path = "measurements/noise/nature/float/utilities/get_rounding_distance.tex")]
/// # Proof Definition
/// Let $D$ denote the space of `size`-dimensional vectors whose elements are in $\mathbb{Z} 2^{k_{min}}$,
/// where $2^{k_{min}}$ is the smallest distance between adjacent non-equal values in `T`.
/// Let $\mathrm{round}_k$ be a function that rounds each element to the nearest multiple of $2^k$,
/// with ties rounding down.
/// Return $\max_{x, x' \in D} ||\mathrm{round}_k(x) - \mathrm{round}_k(x')||_P - ||x - x'||_P$,
/// the increase in the sensitivity due to rounding.
#[cfg_attr(creusot, ensures(forall<r: RBig> result == Ok(r) ==>
    k@ >= T::min_k() && (k@ == T::min_k() || size != None)))]
#[cfg_attr(creusot, ensures(P == 1usize ==> forall<r: RBig> result == Ok(r) ==>
    r.deep_model() == if k@ == T::min_k() { Real::from_int(0) } else {
        (pow2r(k@) - pow2r(T::min_k())) * Real::from_int(match size { Some(n) => n@, None => 0 })
    }))]
#[cfg_attr(creusot, ensures(P == 1usize && k@ >= T::min_k() && (k@ == T::min_k() || size != None)
    ==> exists<r: RBig> result == Ok(r)))]
pub fn get_rounding_distance<T: Float, const P: usize>(
    k: i32,
    size: Option<usize>,
) -> Fallible<RBig>
where
    i32: ExactIntCast<T::Bits>,
{
    let k_min = get_min_k::<T>();
    #[cfg(creusot)]
    proof_assert!(float_grid::<T>());
    if k < k_min {
        return fallible!(FailedFunction, "k ({k}) must not be smaller than {k_min}");
    }

    #[cfg(creusot)]
    proof_assert!(k@ > k_min@ ==> pow2r_lt(k_min@, k@));

    // input has granularity 2^{k_min} (subnormal float precision)
    let input_gran = x_mul_2k(RBig::from(1usize), k_min);

    // discretization rounds to the nearest 2^k
    let output_gran = x_mul_2k(RBig::from(1usize), k);

    // the worst-case increase in sensitivity due to discretization is
    //     the range, minus the smallest step in the range
    let mut distance = output_gran - input_gran;
    #[cfg(creusot)]
    proof_assert!(distance.deep_model() == pow2r(k@) - pow2r(k_min@));
    #[cfg(creusot)]
    proof_assert!(distance.deep_model() == Real::from_int(0) ==> k@ == k_min@);

    // rounding may occur on all vector elements
    if !distance.is_zero() {
        let size = size.ok_or_else(|| {
            err!(
                MakeMeasurement,
                "domain size must be known if discretization is not exact"
            )
        })?;

        let factor = match P {
            1 => RBig::from(size),
            2 => RBig::try_from(f64::inf_cast(size)?.inf_sqrt()?)?,
            _ => return fallible!(MakeMeasurement, "norm ({P}) must be one or two"),
        };
        #[cfg(creusot)]
        proof_assert!(P == 1usize ==> factor.deep_model() == Real::from_int(size@));
        distance *= factor;
        #[cfg(creusot)]
        proof_assert!(P == 1usize ==>
            distance.deep_model() == (pow2r(k@) - pow2r(T::min_k())) * Real::from_int(size@));
    }
    #[cfg(creusot)]
    proof_assert!(P == 1usize ==> distance.deep_model() == if k@ == T::min_k() { Real::from_int(0) } else {
        (pow2r(k@) - pow2r(T::min_k())) * Real::from_int(match size { Some(n) => n@, None => 0 })
    });
    Ok(distance)
}

#[proven(proof_path = "measurements/noise/nature/float/utilities/x_mul_2k.tex")]
/// # Proof Definition
/// `k` must not be `i32::MIN`.
///
/// Return `x * 2^k`.
#[cfg_attr(creusot, requires(k@ > i32::MIN@))]
#[cfg_attr(creusot, ensures(result.deep_model() == x.deep_model() * pow2r(k@)))]
pub fn x_mul_2k(x: RBig, k: i32) -> RBig {
    let (mut num, mut den) = x.into_parts();
    #[cfg(creusot)]
    proof_assert!(dashu_facts() && pow2r_scale(num.deep_model(), den.deep_model(), k@));
    if k < 0 {
        // negation of i32::MIN is undefined
        den <<= -k as usize;
    } else {
        num <<= k as usize;
    }

    RBig::from_parts(num, den)
}

/// # Proof Definition
/// Return `Err(e)` if scale is not finite,
/// otherwise return `Ok(scale * 2^-k)`
#[cfg_attr(creusot, ensures(forall<r: RBig> result == Ok(r) ==>
    scale.finite() && r.deep_model() == scale.real() * pow2r(-k@)))]
#[cfg_attr(creusot, ensures(k@ > i32::MIN@ && scale.finite() ==> exists<r: RBig> result == Ok(r)))]
pub fn integerize_scale(scale: f64, k: i32) -> Fallible<RBig> {
    if k == i32::MIN {
        return fallible!(MakeTransformation, "k ({k}) must not be i32::MIN");
    }

    let scale = RBig::try_from(scale)
        .map_err(|_| err!(MakeTransformation, "scale ({scale}) must be finite"))?;

    Ok(x_mul_2k(scale, -k))
}
