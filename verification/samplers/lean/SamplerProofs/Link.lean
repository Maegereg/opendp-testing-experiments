/-
The link between the sampler proofs and the mechanism theorem (`verification/lean`, phase 2).

The mechanism theorem `OpenDP.Laplace.laplace_mechanism` is stated for noise drawn from
`OpenDP.Laplace.discreteLaplace s`. Here:

* `lap_eq_discreteLaplace`: the distribution the sampler proofs reach is that `PMF`.
* `sampler_discreteLaplace`: the extracted `sample_discrete_laplace` is within `ε` of it.
* `sampler_mechanism`: adding one sample of the extracted sampler to `x` or to `x'` (within
  distance `d`) gives outputs whose probabilities of any set `T` satisfy
  `Pr[x + Z ∈ T] ≤ e^o (Pr[x' + Z ∈ T] + ε)`, for every privacy loss `o` the privacy map may
  return (`LaplaceBound`): the mechanism theorem, applied to the extracted sampler.
-/
import OpenDPVerification.Laplace
import SamplerProofs.DiscreteLaplace

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

open Classical

/-- The sampler's target is phase 2's discrete Laplace distribution. -/
theorem lap_eq_discreteLaplace {s : ℝ} (hs : 0 < s) (z : ℤ) :
    lap (Real.exp (-(1 / s))) (.Ok z) = OpenDP.Laplace.discreteLaplace s z := by
  rw [OpenDP.Laplace.discreteLaplace_apply hs, OpenDP.Laplace.mass,
    OpenDP.Laplace.normalizer, OpenDP.Laplace.weight_eq_pow, OpenDP.Laplace.ratio, neg_div]
  rfl

/-- The extracted sampler. -/
noncomputable def sampler (s : ℚ) : Prog ResI := fun t =>
  traits.samplers.cks20.sample_discrete_laplace_with tapeSource t s

/-- **The extracted `sample_discrete_laplace(scale)` is within `epsLap D` of phase 2's
`discreteLaplace scale`**, and never above it. -/
theorem sampler_discreteLaplace {s : ℚ} (hs : 0 < s) (hsz : Nat.size s.num.natAbs < bitBound)
    {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size s.num.natAbs ≤ D) (z : ℤ) :
    mass (sampler s) (.Ok z) ≤ OpenDP.Laplace.discreteLaplace s z ∧
      OpenDP.Laplace.discreteLaplace s z ≤ mass (sampler s) (.Ok z) + epsLap D := by
  rw [← lap_eq_discreteLaplace (by exact_mod_cast hs)]
  exact discrete_laplace_close hs hsz hD1 hD z

/-- `Approx` for sets: within `ε` of a probability distribution `ν` on every set. -/
theorem Approx.close_set {α : Type} {f : Prog α} {ν : α → ℝ≥0∞} {ε : ℝ≥0∞} (h : Approx f ν ε)
    (hν : ∑' a, ν a = 1) (S : Set α) :
    ∑' a, S.indicator ν a ≤ ∑' a, S.indicator (mass f) a + ε := by
  obtain ⟨μ, h1, h2, h3⟩ := h
  have hμ : mass f = μ := funext fun a => (h1.eq_mass a).symm
  rw [hμ]
  have hsplit : ∀ g : α → ℝ≥0∞, ∑' a, g a = ∑' a, S.indicator g a + ∑' a, Sᶜ.indicator g a :=
    fun g => by rw [← ENNReal.tsum_add]; exact tsum_congr fun a => (S.indicator_self_add_compl_apply g a).symm
  have hle : ∀ T : Set α, ∑' a, T.indicator μ a ≤ ∑' a, T.indicator ν a := fun T =>
    ENNReal.tsum_le_tsum fun a => Set.indicator_le_indicator (h2 a)
  have hfin : ∑' a, Sᶜ.indicator ν a ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hν, hsplit ν]
    exact le_add_self
  have : ∑' a, S.indicator ν a + ∑' a, Sᶜ.indicator ν a ≤
      ∑' a, S.indicator μ a + ε + ∑' a, Sᶜ.indicator ν a := by
    calc _ = 1 := by rw [← hsplit ν, hν]
      _ ≤ ∑' a, μ a + ε := h3
      _ = ∑' a, S.indicator μ a + ∑' a, Sᶜ.indicator μ a + ε := by rw [← hsplit μ]
      _ ≤ ∑' a, S.indicator μ a + ∑' a, Sᶜ.indicator ν a + ε :=
          add_le_add (add_le_add le_rfl (hle Sᶜ)) le_rfl
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).mp this

/-- The probability that `x + Z ∈ T`, for `Z` drawn by the extracted sampler. -/
noncomputable def shiftProb (s : ℚ) (x : ℤ) (T : Set ℤ) : ℝ≥0∞ :=
  ∑' y, T.indicator (fun y => mass (sampler s) (.Ok (y - x))) y

/-- The probability that `x + Z ∈ T`, for `Z` drawn from `discreteLaplace s`. -/
noncomputable def shiftProbDL (s : ℝ) (x : ℤ) (T : Set ℤ) : ℝ≥0∞ :=
  ∑' y, T.indicator (fun y => OpenDP.Laplace.discreteLaplace s (y - x)) y

/-- Phase 2's mechanism, on one coordinate. -/
theorem shiftProbDL_le {s d o : ℝ} (hb : OpenDP.Laplace.LaplaceBound d s (some o)) {x x' : ℤ}
    (hx : |(x : ℝ) - x'| ≤ d) (T : Set ℤ) :
    shiftProbDL s x T ≤ ENNReal.ofReal (Real.exp o) * shiftProbDL s x' T := by
  have h := OpenDP.Laplace.laplace_mechanism hb (n := 1) (fun _ => x) (fun _ => x')
    (by simpa [OpenDP.Laplace.l1] using hx) ((fun v : Fin 1 → ℤ => v 0) ⁻¹' T)
  -- Vectors of length 1 are integers.
  have hconv : ∀ x : ℤ, (OpenDP.Laplace.addNoise (OpenDP.Laplace.discreteLaplace s)
      (fun _ => x)).toOuterMeasure ((fun v : Fin 1 → ℤ => v 0) ⁻¹' T) = shiftProbDL s x T := by
    intro x
    rw [PMF.toOuterMeasure_apply, shiftProbDL, ← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
    refine tsum_congr fun y => ?_
    simp only [Set.indicator, Set.mem_preimage, Equiv.funUnique_symm_apply,
      OpenDP.Laplace.addNoise_apply, OpenDP.Laplace.iid_apply, Fin.prod_univ_one]
    rfl
  rwa [hconv, hconv] at h

/-- **The discrete Laplace mechanism with the extracted sampler.** If `x`, `x'` are within
distance `d` and the privacy map's output `o` satisfies `laplace_bound(d, scale, o)`, then for
every set `T`, `Pr[x + Z ∈ T] ≤ e^o (Pr[x' + Z ∈ T] + ε)`, `Z` drawn by the extracted
`sample_discrete_laplace(scale)` and `ε = epsLap D ≤ 72 / M!`. -/
theorem sampler_mechanism {s : ℚ} (hs : 0 < s) (hsz : Nat.size s.num.natAbs < bitBound)
    {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size s.num.natAbs ≤ D) {d o : ℝ}
    (hb : OpenDP.Laplace.LaplaceBound d s (some o)) {x x' : ℤ} (hx : |(x : ℝ) - x'| ≤ d)
    (T : Set ℤ) :
    shiftProb s x T ≤ ENNReal.ofReal (Real.exp o) * (shiftProb s x' T + epsLap D) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  -- The sampler is below `discreteLaplace` pointwise ...
  have h1 : shiftProb s x T ≤ shiftProbDL s x T :=
    ENNReal.tsum_le_tsum fun y => Set.indicator_le_indicator
      (sampler_discreteLaplace hs hsz hD1 hD (y - x)).1
  -- ... and within `ε` of it on every set.
  have h2 : shiftProbDL s x' T ≤ shiftProb s x' T + epsLap D := by
    have hr1 : Real.exp (-(1 / (s : ℝ))) < 1 :=
      (Real.exp_lt_exp.mpr (show -(1 / (s : ℝ)) < 0 by
        have : 0 < 1 / (s : ℝ) := by positivity
        linarith)).trans_eq Real.exp_zero
    have hc := (discrete_laplace_approx hs hsz hD1 hD).close_set
      (tsum_lap (Real.exp_nonneg _) hr1) {r | ∃ z, r = .Ok z ∧ z + x' ∈ T}
    -- Sums over the results `Ok z` with `z + x' ∈ T` are sums over `y = z + x' ∈ T`.
    have hreindex : ∀ g : ResI → ℝ≥0∞, (∀ e, g (.Err e) = g (.Err e)) →
        ∑' r, {r : ResI | ∃ z, r = .Ok z ∧ z + x' ∈ T}.indicator g r =
          ∑' y, T.indicator (fun y => g (.Ok (y - x'))) y := by
      intro g _
      rw [tsum_res]
      have herr : ∀ e, {r : ResI | ∃ z, r = .Ok z ∧ z + x' ∈ T}.indicator g (.Err e) = 0 :=
        fun e => Set.indicator_of_notMem (by simp) _
      simp only [herr, tsum_zero, add_zero]
      rw [← (Equiv.subRight x').tsum_eq]
      refine tsum_congr fun y => ?_
      simp only [Equiv.subRight_apply, Set.indicator,
        core.result.Result.Ok.injEq, exists_eq_left', sub_add_cancel, Set.mem_ofPred_eq]
    rw [hreindex _ (fun _ => rfl), hreindex _ (fun _ => rfl)] at hc
    simp only [shiftProbDL, shiftProb, ← lap_eq_discreteLaplace hs']
    exact hc
  calc shiftProb s x T ≤ shiftProbDL s x T := h1
    _ ≤ ENNReal.ofReal (Real.exp o) * shiftProbDL s x' T := shiftProbDL_le hb hx T
    _ ≤ _ := by gcongr

end OpenDP.Samplers
