//! OpenDP's discrete Laplace sampler (`rust/src/traits/samplers`), with the randomness source
//! passed explicitly as `rng: &mut R` instead of the global `fill_bytes`, so that Aeneas threads
//! its state through every call. Otherwise the code is OpenDP's, except where marked.
use dashu::{
    base::BitTest,
    integer::{IBig, UBig},
    rational::RBig,
};

#[derive(Debug)]
pub enum ErrorVariant {
    FailedFunction,
}

/// OpenDP's `Error` without the message and backtrace, which do not affect the output.
#[derive(Debug)]
pub struct Error {
    pub variant: ErrorVariant,
}

pub type Fallible<T> = Result<T, Error>;

/// The source of random bytes (OpenDP: `fill_bytes`).
pub trait RandomSource {
    fn fill_bytes(&mut self, buffer: &mut [u8]) -> Fallible<()>;
}

pub fn sample_standard_bernoulli<R: RandomSource>(rng: &mut R) -> Fallible<bool> {
    let mut buffer = [0u8; 1];
    rng.fill_bytes(&mut buffer)?;
    Ok(buffer[0] & 1 == 1)
}

pub fn sample_uniform_ubig_below<R: RandomSource>(rng: &mut R, upper: UBig) -> Fallible<UBig> {
    // ceil(ceil(log_2(upper)) / 8)
    let byte_len = upper.bit_len().div_ceil(8);

    // sample % upper is unbiased for any sample < threshold, because
    // max - max % upper evenly folds into [0, upper), max // upper times
    let max = UBig::from_be_bytes(&vec![u8::MAX; byte_len]);
    let threshold = &max - &max % &upper;

    let mut buffer = vec![0; byte_len];

    Ok(loop {
        rng.fill_bytes(&mut buffer)?;

        let sample = UBig::from_be_bytes(&buffer);
        if sample < threshold {
            break sample % &upper;
        }
    })
}

pub fn sample_bernoulli_rational<R: RandomSource>(rng: &mut R, prob: RBig) -> Fallible<bool> {
    let (numer, denom) = prob.into_parts();
    let (dashu::base::Sign::Positive, numer) = numer.into_parts() else {
        return Err(Error { variant: ErrorVariant::FailedFunction });
    };
    if numer > denom {
        return Err(Error { variant: ErrorVariant::FailedFunction });
    }
    sample_uniform_ubig_below(rng, denom).map(|s| numer > s)
}

fn sample_bernoulli_exp1<R: RandomSource>(rng: &mut R, x: RBig) -> Fallible<bool> {
    let mut k = UBig::ONE;
    loop {
        if sample_bernoulli_rational(rng, x.clone() / &k)? {
            k += UBig::ONE;
        } else {
            return Ok(k % 2u8 == 1);
        }
    }
}

pub fn sample_bernoulli_exp<R: RandomSource>(rng: &mut R, mut x: RBig) -> Fallible<bool> {
    while x > RBig::ONE {
        if sample_bernoulli_exp1(rng, 1.into())? {
            x -= RBig::ONE;
        } else {
            return Ok(false);
        }
    }
    sample_bernoulli_exp1(rng, x)
}

fn sample_geometric_exp_slow<R: RandomSource>(rng: &mut R, x: RBig) -> Fallible<UBig> {
    let mut k = UBig::ZERO;
    loop {
        if sample_bernoulli_exp(rng, x.clone())? {
            k += UBig::ONE;
        } else {
            return Ok(k);
        }
    }
}

pub fn sample_geometric_exp_fast<R: RandomSource>(rng: &mut R, x: RBig) -> Fallible<UBig> {
    if x.is_zero() {
        return Ok(UBig::ZERO);
    }

    let (numer, denom) = x.into_parts();
    let mut u = sample_uniform_ubig_below(rng, denom.clone())?;
    // Changed for Aeneas, which rejects a loop with both a `break` and an early return (`?`)
    // when the code after it branches: the code after the loop moves into the accepting branch.
    loop {
        let accept = sample_bernoulli_exp(rng, RBig::from_parts(u.as_ibig().clone(), denom.clone()))?;
        if accept {
            let v2 = sample_geometric_exp_slow(rng, RBig::ONE)?;
            return Ok((v2 * denom + u) / numer.into_parts().1);
        }
        u = sample_uniform_ubig_below(rng, denom.clone())?;
    }
}

pub fn sample_discrete_laplace<R: RandomSource>(rng: &mut R, scale: RBig) -> Fallible<IBig> {
    if scale.is_zero() {
        return Ok(0.into());
    }
    let (numer, denom) = scale.into_parts();
    let inv_scale = RBig::from_parts(denom.as_ibig().clone(), numer.into_parts().1);

    loop {
        let positive = sample_standard_bernoulli(rng)?;
        let magnitude = sample_geometric_exp_fast(rng, inv_scale.clone())?
            .as_ibig()
            .clone();
        if positive || !magnitude.is_zero() {
            return Ok(if positive { magnitude } else { -magnitude });
        }
    }
}
