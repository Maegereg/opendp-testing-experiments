//! Various transformation constructors.
//!
//! The different [`crate::core::Transformation`] implementations in this module are accessed by calling the appropriate constructor function.
//! Constructors are named in the form `make_xxx()`, where `xxx` indicates what the resulting `Transformation` does.

#[cfg(all(feature = "contrib", feature = "polars"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod make_stable_lazyframe;
#[cfg(all(feature = "contrib", feature = "polars"))]
pub use make_stable_lazyframe::*;

#[cfg(all(feature = "contrib", feature = "polars"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod make_stable_expr;
#[cfg(all(feature = "contrib", feature = "polars"))]
pub use make_stable_expr::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod covariance;
#[cfg(feature = "contrib")]
pub use covariance::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod b_ary_tree;
#[cfg(feature = "contrib")]
pub use b_ary_tree::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod dataframe;
#[cfg(feature = "contrib")]
pub use dataframe::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
pub mod quantile_score_candidates;
#[cfg(feature = "contrib")]
pub use quantile_score_candidates::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod manipulation;
#[cfg(feature = "contrib")]
pub use manipulation::*;

#[cfg(feature = "contrib")]
mod sum;
#[cfg(feature = "contrib")]
pub use sum::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod sum_of_squared_deviations;
#[cfg(feature = "contrib")]
pub use sum_of_squared_deviations::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod count;
#[cfg(feature = "contrib")]
pub use count::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod count_cdf;
#[cfg(feature = "contrib")]
pub use count_cdf::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod mean;
#[cfg(feature = "contrib")]
pub use mean::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod variance;
#[cfg(feature = "contrib")]
pub use variance::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod impute;
#[cfg(feature = "contrib")]
pub use impute::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod index;
#[cfg(feature = "contrib")]
pub use index::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod lipschitz_mul;
#[cfg(feature = "contrib")]
pub use lipschitz_mul::*;

#[cfg(feature = "ffi")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod make_user_transformation;
#[cfg(feature = "ffi")]
pub use make_user_transformation::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod clamp;
#[cfg(feature = "contrib")]
pub use clamp::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod cast;
#[cfg(feature = "contrib")]
pub use cast::*;

#[cfg(feature = "contrib")]
mod cast_metric;
#[cfg(feature = "contrib")]
pub use cast_metric::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod resize;
#[cfg(feature = "contrib")]
pub use resize::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod scalar_to_vector;
#[cfg(feature = "contrib")]
pub use scalar_to_vector::*;
