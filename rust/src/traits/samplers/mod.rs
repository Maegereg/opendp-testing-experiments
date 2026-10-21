//! Traits for sampling from probability distributions.

#[cfg(test)]
pub(crate) mod test;

mod bernoulli;
pub use bernoulli::*;

mod cks20;
pub use cks20::*;

mod geometric;
pub use geometric::*;

mod psrn;
pub use psrn::*;

mod uniform;
pub use uniform::*;

use rand::RngCore;
use rand::prelude::SliceRandom;

use crate::error::Fallible;

/// Fill a byte buffer with random bits.
///
/// # Proof Definition
/// For any input `buffer`, fill the `buffer` with random bits, where each bit is an iid draw from Bernoulli(p=0.5).
/// Return `Err(e)` if there is insufficient system entropy, otherwise return `Ok(())`.
#[cfg(feature = "use-openssl")]
pub fn fill_bytes(buffer: &mut [u8]) -> Fallible<()> {
    // "RAND_priv_bytes() has the same semantics as RAND_bytes(). It is intended to be used for generating values that should remain private."
    // https://docs.openssl.org/3.0/man3/RAND_bytes/
    use openssl::rand::rand_priv_bytes;
    if let Err(e) = rand_priv_bytes(buffer) {
        fallible!(FailedFunction, "OpenSSL error: {:?}", e)
    } else {
        Ok(())
    }
}

/// Non-securely fill a byte buffer with random bits.
///
/// Enable `use-openssl` for a secure implementation.
#[cfg(not(feature = "use-openssl"))]
pub fn fill_bytes(buffer: &mut [u8]) -> Fallible<()> {
    use rand::Rng;
    if let Err(e) = rand::thread_rng().try_fill(buffer) {
        fallible!(FailedFunction, "Rand error: {:?}", e)
    } else {
        Ok(())
    }
}

/// An OpenDP random number generator that implements [`rand::RngCore`].
pub(crate) struct GeneratorOpenDP {
    /// If an error happens while sampling, it is packed into this struct and thrown later.
    pub error: Fallible<()>,
}

impl GeneratorOpenDP {
    pub fn new() -> Self {
        GeneratorOpenDP { error: Ok(()) }
    }
}
impl Default for GeneratorOpenDP {
    fn default() -> Self {
        Self::new()
    }
}

impl RngCore for GeneratorOpenDP {
    fn next_u32(&mut self) -> u32 {
        let mut buffer = [0u8; 4];
        self.fill_bytes(&mut buffer);
        u32::from_ne_bytes(buffer)
    }

    fn next_u64(&mut self) -> u64 {
        let mut buffer = [0u8; 8];
        self.fill_bytes(&mut buffer);
        u64::from_ne_bytes(buffer)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        if let Err(e) = fill_bytes(dest) {
            self.error = Err(e)
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        fill_bytes(dest).map_err(rand::Error::new)
    }
}

/// Shuffle a mutable reference to a collection.
pub trait Shuffle {
    /// # Proof Definition
    /// For any input `self` of type `Self`,
    /// mutate `self` such that the elements within are ordered randomly.
    /// Returns `Err(e)` if there is insufficient system entropy,
    /// or `Ok(())` otherwise.
    #[cfg_attr(creusot, creusot_std::macros::ensures(result == Ok(()) ==> (*self).reorders(^self)))]
    fn shuffle(&mut self) -> Fallible<()>;

    /// Ghost model: `out` holds the elements of `self`, in some order.
    #[cfg(creusot)]
    #[creusot_std::macros::logic]
    fn reorders(self, out: Self) -> bool;
}
impl<T> Shuffle for Vec<T> {
    // Trusted (as is this module): `SliceRandom::shuffle` permutes the slice.
    #[cfg_attr(creusot, creusot_std::macros::ensures(result == Ok(()) ==> (*self).reorders(^self)))]
    fn shuffle(&mut self) -> Fallible<()> {
        let mut rng = GeneratorOpenDP::new();
        SliceRandom::shuffle(self.as_mut_slice(), &mut rng);
        rng.error
    }

    // Visible only in this module (see `vec_reorders`), as `permutation_of` slows down unrelated proofs.
    #[cfg(creusot)]
    #[creusot_std::macros::logic(open(self))]
    fn reorders(self, out: Self) -> bool {
        pearlite! { out@.permutation_of(self@) }
    }
}

/// Shuffling a vector permutes its elements.
#[cfg(creusot)]
#[creusot_std::macros::logic]
#[creusot_std::macros::ensures(a.reorders(b) == b@.permutation_of(a@))]
pub fn vec_reorders<T>(a: Vec<T>, b: Vec<T>) {}
