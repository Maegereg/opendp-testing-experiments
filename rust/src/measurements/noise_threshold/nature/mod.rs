use crate::{
    core::Domain,
    domains::{AtomDomain, MapDomain},
    measurements::NoiseDomain,
    traits::{CheckAtom, Hashable},
};

mod float;
mod integer;

#[cfg(creusot)]
mod proof;
#[cfg(creusot)]
pub use proof::*;

use std::collections::HashMap;

use crate::verification::MaybeDeepModel;
#[cfg(creusot)]
use creusot_std::{
    macros::{ensures, requires, trusted},
    prelude::inv,
    std::ops::{FnExt, FnOnceExt},
};

/// Applies `f` to every value of `map`, keeping the keys.
// Trusted: `HashMap::iter` and `collect` have no specifications here. Assumes that `Eq` and `Hash` on
// `K` agree with equality of deep models (as for `count_by_map`), so that collecting the pairs
// gives back the keys of `map`, each once.
#[cfg_attr(creusot, trusted)]
#[cfg_attr(creusot, requires(forall<v: V> inv(v) ==> f.precondition((&v,))))]
#[cfg_attr(creusot, ensures(forall<k: K::DeepModelTy> result@.contains(k) == map@.contains(k)))]
#[cfg_attr(creusot, ensures(forall<k: K::DeepModelTy> map@.contains(k) ==>
    f.postcondition((&map@[k],), result@[k])))]
pub(crate) fn map_values<K: Hashable + MaybeDeepModel, V, W>(
    map: &HashMap<K, V>,
    f: impl Fn(&V) -> W,
) -> HashMap<K, W> {
    map.iter().map(|(k, v)| (k.clone(), f(v))).collect()
}

impl<DK: Domain, TV: 'static + CheckAtom> NoiseDomain for MapDomain<DK, AtomDomain<TV>>
where
    DK::Carrier: Hashable,
{
    type Atom = TV;
}
