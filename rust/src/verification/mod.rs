//! Support for formal verification with [Creusot](https://github.com/creusot-rs/creusot).
//!
//! `cargo creusot` compiles the crate with `--cfg creusot`.
//! Everything here behaves like plain Rust in normal builds.
//!
//! Creusot specifies `PartialEq::eq` in terms of `DeepModel`,
//! so every type that implements `PartialEq` also needs a `DeepModel` under Creusot.

/// `#[derive(crate::verification::PartialEq)]` is the standard derive in normal builds.
#[cfg(not(creusot))]
pub(crate) use core::cmp::PartialEq;
/// `#[derive(crate::verification::PartialEq)]` is Creusot's derive under Creusot,
/// which also requires each type parameter to have a `DeepModel`.
#[cfg(creusot)]
pub(crate) use creusot_std::std::cmp::PartialEq;

/// A supertrait of [`Domain`](crate::core::Domain), [`Metric`](crate::core::Metric) and
/// [`Measure`](crate::core::Measure) that is `DeepModel` under Creusot, and empty otherwise.
///
/// This lets generic code compare e.g. `VectorDomain<D>` for any `D: Domain`.
#[cfg(creusot)]
#[doc(hidden)]
pub trait MaybeDeepModel: creusot_std::model::DeepModel {}
#[cfg(creusot)]
impl<T: creusot_std::model::DeepModel + ?Sized> MaybeDeepModel for T {}

#[cfg(not(creusot))]
#[doc(hidden)]
pub trait MaybeDeepModel {}
#[cfg(not(creusot))]
impl<T: ?Sized> MaybeDeepModel for T {}

/// A supertrait of [`Integer`](crate::traits::Integer) that, under Creusot,
/// models each integer by the mathematical integer it represents. Empty otherwise.
///
/// This lets generic integer code compare values with `<`, `==`, etc.
#[cfg(creusot)]
#[doc(hidden)]
pub trait MaybeIntModel:
    creusot_std::model::DeepModel<DeepModelTy = creusot_std::logic::Int>
{
}
#[cfg(creusot)]
impl<T: creusot_std::model::DeepModel<DeepModelTy = creusot_std::logic::Int> + ?Sized> MaybeIntModel
    for T
{
}

#[cfg(not(creusot))]
#[doc(hidden)]
pub trait MaybeIntModel {}
#[cfg(not(creusot))]
impl<T: ?Sized> MaybeIntModel for T {}

/// Logical models of datasets, and of distances between them.
#[cfg(creusot)]
pub mod dataset;

/// Sums of integer datasets, and when they can be computed without overflow.
#[cfg(creusot)]
pub mod integer;

/// Ordered datasets, the insert-delete distance, and saturating sums.
#[cfg(creusot)]
pub mod ordered;

/// The real number that a numeric value represents.
///
/// The "Proof Definitions" of OpenDP's arithmetic traits are stated over the reals
/// (e.g. `inf_add` returns `out >= self + v`), so their Creusot contracts are stated via `real`.
/// Under Creusot, every numeric type implements this trait. It is empty otherwise.
#[cfg(creusot)]
#[doc(hidden)]
pub trait RealModel {
    #[creusot_std::macros::logic]
    fn real(self) -> creusot_std::logic::real::Real;
}

#[cfg(not(creusot))]
#[doc(hidden)]
pub trait RealModel {}
#[cfg(not(creusot))]
impl<T: ?Sized> RealModel for T {}

/// Absolute value of a real.
#[cfg(creusot)]
#[creusot_std::macros::logic(open)]
pub fn real_abs(x: creusot_std::logic::real::Real) -> creusot_std::logic::real::Real {
    use creusot_std::logic::real::Real;
    if x >= Real::from_int(0) { x } else { -x }
}

#[cfg(creusot)]
mod real_model {
    use super::RealModel;
    use creusot_std::{logic::real::Real, prelude::*};
    use dashu::{
        float::{FBig, round::Round},
        integer::{IBig, UBig},
        rational::RBig,
    };

    macro_rules! impl_real_model_int {
        ($($ty:ty),*) => ($(impl RealModel for $ty {
            #[logic(open)]
            fn real(self) -> Real {
                pearlite! { Real::from_int(self@) }
            }
        })*)
    }
    impl_real_model_int!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );

    impl RealModel for IBig {
        #[logic(open)]
        fn real(self) -> Real {
            Real::from_int(self.deep_model())
        }
    }
    impl RealModel for UBig {
        #[logic(open)]
        fn real(self) -> Real {
            Real::from_int(self.deep_model())
        }
    }
    impl RealModel for RBig {
        #[logic(open)]
        fn real(self) -> Real {
            self.deep_model()
        }
    }

    // Left uninterpreted for now. Contracts about floats are trusted,
    // and checked for consistency by mutation tests.
    macro_rules! impl_real_model_opaque {
        ([$($generics:tt)*] $ty:ty) => {
            impl<$($generics)*> RealModel for $ty {
                #[logic(opaque)]
                fn real(self) -> Real {
                    dead
                }
            }
        };
    }
    impl_real_model_opaque!([] f32);
    impl_real_model_opaque!([] f64);
    impl_real_model_opaque!([R: Round, const B: u64] FBig<R, B>);
    // Pairs are only compared (by `ProductOrd`) when clamping.
    impl_real_model_opaque!([T1, T2](T1, T2));
}

/// Gives a type whose `PartialEq` ignores all of its data (e.g. it only holds `PhantomData`)
/// a trivial deep model, so that `==` is specified as always true.
#[cfg(creusot)]
macro_rules! unit_deep_model {
    ([$($generics:tt)*] $ty:ty) => {
        impl<$($generics)*> ::creusot_std::model::DeepModel for $ty {
            type DeepModelTy = ();
            #[::creusot_std::macros::logic(open)]
            fn deep_model(self) -> () {}
        }
    };
}
