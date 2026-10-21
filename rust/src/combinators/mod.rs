//! Various combinator constructors.

#[cfg(all(feature = "contrib", feature = "honest-but-curious"))]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod amplify;
#[cfg(all(feature = "contrib", feature = "honest-but-curious"))]
pub use crate::combinators::amplify::*;

#[cfg(feature = "contrib")]
mod chain;
#[cfg(feature = "contrib")]
pub use crate::combinators::chain::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod sequential_composition;
#[cfg(feature = "contrib")]
pub use sequential_composition::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod select_private_candidate;
#[cfg(feature = "contrib")]
pub use select_private_candidate::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod measure_cast;
#[cfg(feature = "contrib")]
pub use crate::combinators::measure_cast::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod privacy_filter;
#[cfg(feature = "contrib")]
pub use privacy_filter::*;

#[cfg(feature = "contrib")]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
mod fix_delta;
#[cfg(feature = "contrib")]
pub use crate::combinators::fix_delta::*;

#[cfg(test)]
#[cfg_attr(creusot, creusot_std::macros::trusted)]
pub mod test;
