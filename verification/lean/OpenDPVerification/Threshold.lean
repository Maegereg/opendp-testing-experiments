/-
The discrete Laplace threshold mechanism (`make_laplace_threshold`): two flaws in its privacy map.

The mechanism adds discrete Laplace noise `Z` of scale `s` to each value `v` of a map, and keeps a
key when `v + Z ≥ T` (for a positive threshold `T`). A key present in `x` with value `v` but absent
from a neighbour `x'` is therefore released with probability `Pr[v + Z ≥ T] = Pr[Z ≥ T - v]`
(`releaseProb_eq`), and never from `x'`. On the event "the key is released", an `(ε, δ)` guarantee
needs `δ ≥ Pr[Z ≥ T - v]`.

* F7: the privacy map computes `δ` (for one such key) from a bound on `Pr[Z > T - Δ∞]`. Both bounds it
  computes, the exact discrete tail `e^{-d/s} / (e^{1/s} + 1)` and the continuous tail `e^{-d/s} / 2`,
  are strictly smaller than the release probability `Pr[Z ≥ d]` at `v = Δ∞`, `d = T - Δ∞`
  (`threshold_delta_too_small`), by the factors `e^{-1/s}` and `(1 + e^{-1/s}) / 2`.
* F8: the input metric treats an absent key as the value 0, so `{k: 0}` and `{}` are at distance 0,
  and the map returns `δ = 0`; but `{k: 0}` releases `k` with probability `Pr[Z ≥ T] > 0`
  (`zero_key_released`).

Both are fixed on the branch: a key is released when `v + Z > T`, and keys with value 0 are dropped
before noise is added. A key with value `v` is then released with probability
`Pr[v + Z > T] = Pr[Z > T - v]` (`releaseProbStrict_eq`), which the discrete tail computed by the
map equals at `v = Δ∞` (`discrete_bound_eq`) and the continuous tail bounds
(`continuous_ge_discrete`, used by the Creusot proof as `tail_facts`).
-/
import OpenDPVerification.Laplace

namespace OpenDP.Threshold

open Real OpenDP.Laplace

/-- `Pr[Z ≥ t]` for `Z` discrete Laplace with scale `s`. -/
noncomputable def tailGe (s : ℝ) (t : ℤ) : ℝ := ∑' z : ℤ, if t ≤ z then mass s z else 0

/-- `Pr[Z > t]`. -/
noncomputable def tailGt (s : ℝ) (t : ℤ) : ℝ := tailGe s (t + 1)

/-- `Pr[v + Z ≥ T]`: the probability that a key with value `v` is released. -/
noncomputable def releaseProb (s : ℝ) (v T : ℤ) : ℝ := ∑' z : ℤ, if T ≤ v + z then mass s z else 0

theorem releaseProb_eq (s : ℝ) (v T : ℤ) : releaseProb s v T = tailGe s (T - v) := by
  unfold releaseProb tailGe
  congr 1
  funext z
  congr 1
  apply propext
  omega

/-- The summand of `tailGe s d` on the naturals. -/
noncomputable def natPart (s : ℝ) (d : ℕ) (n : ℕ) : ℝ := if (d : ℤ) ≤ (n : ℤ) then mass s n else 0

theorem hasSum_natPart {s : ℝ} (hs : 0 < s) (d : ℕ) :
    HasSum (natPart s d) (normalizer s * ratio s ^ d * (1 - ratio s)⁻¹) := by
  have hz : ∑ i ∈ Finset.range d, natPart s d i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : ¬ ((d : ℤ) ≤ (i : ℤ)) := by simp at hi; omega
      simp only [natPart, this, ite_false]
  refine (hasSum_nat_add_iff' d).mp ?_
  rw [hz, sub_zero]
  have := (hasSum_geometric_of_lt_one (ratio_pos s).le (ratio_lt_one hs)).mul_left
    (normalizer s * ratio s ^ d)
  refine this.congr_fun fun n => ?_
  have hle : (d : ℤ) ≤ ((n + d : ℕ) : ℤ) := by omega
  have habs : ((n + d : ℕ) : ℤ).natAbs = n + d := by omega
  simp only [natPart, hle, ite_true, mass, weight_eq_pow, habs, pow_add]
  ring

/-- `Pr[Z ≥ d] = e^{-d/s} / (1 + e^{-1/s})` for `d ≥ 0`. -/
theorem tailGe_nat {s : ℝ} (hs : 0 < s) (d : ℕ) :
    tailGe s d = ratio s ^ d / (1 + ratio s) := by
  have h1 := ratio_lt_one hs
  have hr := ratio_pos s
  have hneg : HasSum (fun n : ℕ => (if (d : ℤ) ≤ -(n + 1 : ℤ) then mass s (-(n + 1 : ℤ)) else 0))
      0 := by
    convert hasSum_zero with n
    have : ¬ ((d : ℤ) ≤ -(n + 1 : ℤ)) := by omega
    simp only [this, ite_false]
  have hall := HasSum.of_nat_of_neg_add_one
    (f := fun z : ℤ => if ((d : ℕ) : ℤ) ≤ z then mass s z else 0) (hasSum_natPart hs d) hneg
  unfold tailGe
  rw [hall.tsum_eq, add_zero, normalizer]
  have hne : (1 : ℝ) - ratio s ≠ 0 := (sub_pos.mpr h1).ne'
  have hne2 : (1 : ℝ) + ratio s ≠ 0 := by linarith
  field_simp

/-- `Pr[Z > d] = e^{-1/s} Pr[Z ≥ d]` for `d ≥ 0`. -/
theorem tailGt_nat {s : ℝ} (hs : 0 < s) (d : ℕ) :
    tailGt s d = ratio s * tailGe s d := by
  unfold tailGt
  have := tailGe_nat hs (d + 1)
  push_cast at this
  rw [this, tailGe_nat hs d, pow_succ]
  ring

/-- The discrete tail bound computed by `conservative_discrete_laplacian_tail_to_alpha`,
`e^{-d/s} / (e^{1/s} + 1)`, is exactly `Pr[Z > d]`. -/
theorem discrete_bound_eq {s : ℝ} (hs : 0 < s) (d : ℕ) :
    exp (-(d : ℝ) / s) / (exp (1 / s) + 1) = tailGt s d := by
  rw [tailGt_nat hs d, tailGe_nat hs d, ratio, ← exp_nat_mul]
  have he : exp (1 / s) = (exp (-1 / s))⁻¹ := by rw [← exp_neg]; ring_nf
  rw [he]
  have hpos := exp_pos (-1 / s)
  field_simp

/-- **F7.** Both tail bounds computed by the privacy map are strictly below the probability that
an unstable key with value `Δ` is released, `Pr[Z ≥ T - Δ]`. -/
theorem threshold_delta_too_small {s : ℝ} (hs : 0 < s) (Δ T : ℤ) (d : ℕ) (hd : (d : ℤ) = T - Δ) :
    exp (-(d : ℝ) / s) / (exp (1 / s) + 1) < releaseProb s Δ T
      ∧ exp (-(d : ℝ) / s) / 2 < releaseProb s Δ T := by
  have h0 := ratio_pos s
  have h1 := ratio_lt_one hs
  rw [releaseProb_eq, ← hd, discrete_bound_eq hs, tailGt_nat hs]
  have hge : 0 < tailGe s d := by
    rw [tailGe_nat hs]; exact div_pos (pow_pos h0 d) (by linarith)
  refine ⟨by nlinarith, ?_⟩
  rw [tailGe_nat hs, ratio, ← exp_nat_mul]
  have : exp (↑d * (-1 / s)) = exp (-(d : ℝ) / s) := by ring_nf
  rw [this]
  have hr := ratio_lt_one hs
  unfold ratio at hr
  exact div_lt_div_of_pos_left (exp_pos _) (by linarith [exp_pos (-1 / s)]) (by linarith)

/-- **F8.** A key with value 0 is released with positive probability, although `{k: 0}` and `{}`
are at distance 0 under the input metric. -/
theorem zero_key_released {s : ℝ} (hs : 0 < s) (T : ℤ) : 0 < releaseProb s 0 T := by
  rw [releaseProb_eq]
  unfold tailGe
  have hsum : Summable (fun z : ℤ => if T - 0 ≤ z then mass s z else 0) :=
    (hasSum_mass hs).summable.of_nonneg_of_le
      (fun z => by split_ifs <;> simp [mass_nonneg hs])
      (fun z => by split_ifs <;> simp [mass_nonneg hs])
  refine lt_of_lt_of_le ?_ (hsum.le_tsum (T - 0) fun z _ => by split_ifs <;> simp [mass_nonneg hs])
  simp only [le_refl, ite_true]
  exact mul_pos (normalizer_pos hs) (exp_pos _)

/-- `Pr[v + Z > T]`: the probability that a key with value `v` is released under the fixed rule. -/
noncomputable def releaseProbStrict (s : ℝ) (v T : ℤ) : ℝ :=
  ∑' z : ℤ, if T < v + z then mass s z else 0

theorem releaseProbStrict_eq (s : ℝ) (v T : ℤ) : releaseProbStrict s v T = tailGt s (T - v) := by
  unfold releaseProbStrict tailGt tailGe
  congr 1
  funext z
  congr 1
  apply propext
  omega

/-- The continuous tail `e^{-d/s} / 2` bounds the discrete tail `Pr[Z > d]`, for `d ≥ 0`. -/
theorem continuous_ge_discrete {s : ℝ} (hs : 0 < s) (d : ℕ) :
    tailGt s d ≤ exp (-(d : ℝ) / s) / 2 := by
  have h0 := ratio_pos s
  have h1 := ratio_lt_one hs
  rw [tailGt_nat hs, tailGe_nat hs]
  have he : exp (-(d : ℝ) / s) = ratio s ^ d := by
    rw [ratio, ← exp_nat_mul]; ring_nf
  rw [he]
  have hp := pow_pos h0 d
  rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/-- Tails are probabilities: non-negative. -/
theorem tailGt_nonneg {s : ℝ} (hs : 0 < s) (d : ℕ) : 0 ≤ tailGt s d := by
  rw [tailGt_nat hs, tailGe_nat hs]
  have h0 := ratio_pos s
  positivity

end OpenDP.Threshold
