//! Various measurement constructors.
//!
//! The different [`crate::core::Measurement`] implementations in this module are accessed by calling the appropriate constructor function.
//! Constructors are named in the form `make_xxx()`, where `xxx` indicates what the resulting `Measurement` does.

#[cfg(all(feature = "contrib", feature = "polars"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod make_private_expr;
#[cfg(all(feature = "contrib", feature = "polars"))]
pub use make_private_expr::*;

#[cfg(all(feature = "contrib", feature = "polars"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod make_private_lazyframe;
#[cfg(all(feature = "contrib", feature = "polars"))]
pub use make_private_lazyframe::*;

#[cfg(all(feature = "honest-but-curious", feature = "ffi"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod make_user_measurement;
#[cfg(all(feature = "honest-but-curious", feature = "ffi"))]
pub use crate::measurements::make_user_measurement::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod private_quantile;
#[cfg(feature = "contrib")]
pub use private_quantile::*;

#[cfg(feature = "contrib")]
mod noise;
#[cfg(feature = "contrib")]
pub use noise::*;

#[cfg(feature = "contrib")]
mod noise_threshold;
#[cfg(feature = "contrib")]
pub use noise_threshold::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod noisy_max;
#[cfg(feature = "contrib")]
pub use noisy_max::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod noisy_top_k;
#[cfg(feature = "contrib")]
pub use noisy_top_k::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod randomized_response;
#[cfg(feature = "contrib")]
pub use randomized_response::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod randomized_response_bitvec;
#[cfg(feature = "contrib")]
pub use randomized_response_bitvec::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod canonical_noise;
#[cfg(feature = "contrib")]
pub use canonical_noise::*;

#[cfg(all(feature = "idealized-numerics", feature = "contrib"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod alp;
#[cfg(all(feature = "idealized-numerics", feature = "contrib"))]
pub use alp::*;
