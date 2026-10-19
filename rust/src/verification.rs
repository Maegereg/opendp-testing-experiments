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
