/-
The discrete Laplace mechanism on integer vectors under the L1 distance: OpenDP's
`NoisePrivacyMap<L1Distance<RBig>, MaxDivergence> for ZExpFamily<1>`.

This replaces the cited axiom `laplace_mechanism` (`rust/src/measurements/noise/distribution/laplace/proof.rs`).
The Creusot proof shows that the privacy map's outputs satisfy `laplace_bound`; `LaplaceBound` is its
counterpart here, and `laplace_mechanism` proves the Proof Definition of `NoisePrivacyMap` from it:
for integer vectors `x`, `x'` of the same length within L1 distance `d`, the outputs of
`x + Z` and `x' + Z`, with `Z` a vector of independent discrete Laplace samples, are within
max-divergence `o`.

Modeling choices:
* The discrete Laplace distribution with scale `s > 0` has mass
  `(1 - e^{-1/s}) / (1 + e^{-1/s}) e^{-|z|/s}` (`discreteLaplace`); proved to sum to 1. With scale
  `0` it is the point mass at `0` (`ZExpFamily`'s Proof Definition).
* Independent samples: the vector of noise has the product mass (`iid`).
* An `f64` privacy loss is `some o` when finite with value `o`, and `none` when it is `+∞`.
* Max-divergence at most `o` is the set-wise bound `P(S) ≤ e^o Q(S)` for every set `S`; any pair
  of distributions is within `+∞`.
-/
import Mathlib

namespace OpenDP.Laplace

open Real

/-! ### The discrete Laplace distribution -/

/-- `e^{-1/s}`, the ratio of the geometric tails. -/
noncomputable def ratio (s : ℝ) : ℝ := exp (-1 / s)

theorem ratio_pos (s : ℝ) : 0 < ratio s := exp_pos _

theorem ratio_lt_one {s : ℝ} (hs : 0 < s) : ratio s < 1 :=
  by rw [ratio, ← exp_zero]; exact exp_lt_exp.mpr (div_neg_of_neg_of_pos (by norm_num) hs)

/-- The unnormalized mass `e^{-|z|/s}`. -/
noncomputable def weight (s : ℝ) (z : ℤ) : ℝ := exp (-|(z : ℝ)| / s)

theorem weight_eq_pow (s : ℝ) (z : ℤ) : weight s z = ratio s ^ z.natAbs := by
  rw [weight, ratio, ← exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
  congr 1
  ring

/-- `∑_z e^{-|z|/s} = (1 + r) / (1 - r)` with `r = e^{-1/s}`. -/
theorem hasSum_weight {s : ℝ} (hs : 0 < s) :
    HasSum (weight s) ((1 + ratio s) / (1 - ratio s)) := by
  have h0 := (ratio_pos s).le
  have h1 := ratio_lt_one hs
  have hg := hasSum_geometric_of_lt_one h0 h1
  have hpos : HasSum (fun n : ℕ => weight s n) (1 - ratio s)⁻¹ := by
    simpa [weight_eq_pow] using hg
  have hneg : HasSum (fun n : ℕ => weight s (-(n + 1 : ℤ))) (ratio s * (1 - ratio s)⁻¹) := by
    have := hg.mul_left (ratio s)
    refine this.congr_fun fun n => ?_
    rw [weight_eq_pow, ← pow_succ', show (-(n + 1 : ℤ)).natAbs = n + 1 by omega]
  convert hpos.of_nat_of_neg_add_one hneg using 1
  field_simp [(sub_pos.mpr h1).ne']

/-- The normalizing constant `(1 - e^{-1/s}) / (1 + e^{-1/s})`. -/
noncomputable def normalizer (s : ℝ) : ℝ := (1 - ratio s) / (1 + ratio s)

theorem normalizer_pos {s : ℝ} (hs : 0 < s) : 0 < normalizer s :=
  div_pos (sub_pos.mpr (ratio_lt_one hs)) (by linarith [ratio_pos s])

/-- The mass of the discrete Laplace distribution, `(1 - e^{-1/s}) / (1 + e^{-1/s}) e^{-|z|/s}`. -/
noncomputable def mass (s : ℝ) (z : ℤ) : ℝ := normalizer s * weight s z

theorem mass_nonneg {s : ℝ} (hs : 0 < s) (z : ℤ) : 0 ≤ mass s z :=
  mul_nonneg (normalizer_pos hs).le (exp_pos _).le

theorem hasSum_mass {s : ℝ} (hs : 0 < s) : HasSum (mass s) 1 := by
  have h1 := ratio_lt_one hs
  have h := (hasSum_weight hs).mul_left (normalizer s)
  rwa [show normalizer s * ((1 + ratio s) / (1 - ratio s)) = 1 by
    rw [normalizer]
    field_simp [(sub_pos.mpr h1).ne', (by linarith [ratio_pos s] : 1 + ratio s ≠ 0)]] at h

/-- The discrete Laplace distribution with scale `s > 0`. -/
noncomputable def discreteLaplacePos {s : ℝ} (hs : 0 < s) : PMF ℤ :=
  ⟨fun z => ENNReal.ofReal (mass s z), by
    rw [ENNReal.summable.hasSum_iff, ← ENNReal.ofReal_tsum_of_nonneg (mass_nonneg hs)
      (hasSum_mass hs).summable, (hasSum_mass hs).tsum_eq, ENNReal.ofReal_one]⟩

/-- `ZExpFamily<1>` with scale `s ≥ 0`: the discrete Laplace distribution, or the point mass at `0`
when `s = 0`. -/
noncomputable def discreteLaplace (s : ℝ) : PMF ℤ :=
  if hs : 0 < s then discreteLaplacePos hs else PMF.pure 0

theorem discreteLaplace_apply {s : ℝ} (hs : 0 < s) (z : ℤ) :
    discreteLaplace s z = ENNReal.ofReal (mass s z) := by
  simp only [discreteLaplace, hs, ↓reduceDIte]
  rfl

/-! ### Independent noise on vectors -/

/-- `∑_v ∏_i f(v_i) = (∑_z f(z))^n`. -/
theorem tsum_prod_pi (f : ℤ → ENNReal) :
    ∀ n : ℕ, ∑' v : Fin n → ℤ, ∏ i, f (v i) = (∑' z, f z) ^ n
  | 0 => by simp
  | n + 1 => by
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod']
    simp only [ENNReal.tsum_mul_left]
    rw [tsum_prod_pi f n, ENNReal.tsum_mul_right, pow_succ']

/-- `n` independent samples of `p`. -/
noncomputable def iid (p : PMF ℤ) (n : ℕ) : PMF (Fin n → ℤ) :=
  ⟨fun v => ∏ i, p (v i), by
    rw [ENNReal.summable.hasSum_iff, tsum_prod_pi, p.tsum_coe, one_pow]⟩

theorem iid_apply (p : PMF ℤ) {n : ℕ} (v : Fin n → ℤ) : iid p n v = ∏ i, p (v i) := rfl

/-- The output distribution of `function(x) = x + Z`, `Z` a vector of `n` independent samples of
`p` (`noise_function` applying `Sample::sample` to each element). -/
noncomputable def addNoise (p : PMF ℤ) {n : ℕ} (x : Fin n → ℤ) : PMF (Fin n → ℤ) :=
  (iid p n).map (x + ·)

theorem addNoise_apply (p : PMF ℤ) {n : ℕ} (x y : Fin n → ℤ) :
    addNoise p x y = iid p n (y - x) := by
  rw [addNoise, PMF.map_apply, tsum_eq_single (y - x)]
  · simp
  · intro a ha
    simp only [ite_eq_right_iff]
    rintro rfl
    exact absurd (by simp) ha

/-! ### Metrics and measures -/

/-- The L1 distance between integer vectors of the same length. -/
noncomputable def l1 {n : ℕ} (x x' : Fin n → ℤ) : ℝ := ∑ i, |((x i : ℝ) - x' i)|

/-- `P` and `Q` are within max-divergence `o` (`none` is `+∞`):
`D_∞(P ‖ Q) = sup_S ln (P(S) / Q(S)) ≤ o`. -/
def MaxDivClose {α : Type*} (P Q : PMF α) : Option ℝ → Prop
  | none => True
  | some o => ∀ S : Set α, P.toOuterMeasure S ≤ ENNReal.ofReal (exp o) * Q.toOuterMeasure S

/-- A pointwise bound on the masses bounds the max-divergence. -/
theorem maxDivClose_of_pointwise {α : Type*} {P Q : PMF α} {o : ℝ}
    (h : ∀ y, P y ≤ ENNReal.ofReal (exp o) * Q y) : MaxDivClose P Q (some o) := by
  intro S
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases hy : y ∈ S <;> simp [Set.indicator, hy, h y]

/-- `laplace_bound(d, s, o)` from the Creusot proof: the privacy map's output `o` at sensitivity
`d` and scale `s`. A finite `o` is `0` at `d = 0`, or at least `d / s` with `s > 0`; `o = +∞` is
always a valid bound. -/
def LaplaceBound (d s : ℝ) : Option ℝ → Prop
  | none => 0 ≤ d
  | some o => 0 ≤ d ∧ ((d = 0 ∧ o = 0) ∨ (0 < s ∧ d / s ≤ o))

/-! ### The mechanism -/

/-- Reverse triangle inequality for one coordinate:
`e^{-|y - x|/s} ≤ e^{|x - x'|/s} e^{-|y - x'|/s}`. -/
theorem mass_shift_le {s : ℝ} (hs : 0 < s) (a b : ℤ) :
    mass s a ≤ exp (|((b : ℝ) - a)| / s) * mass s b := by
  rw [mass, mass, mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (normalizer_pos hs).le
  rw [weight, weight, ← exp_add]
  refine exp_le_exp.mpr ?_
  rw [← add_div, div_le_div_iff_of_pos_right hs]
  have := abs_sub_abs_le_abs_sub (b : ℝ) (a : ℝ)
  linarith

/-- The pointwise privacy-loss bound: `Pr[x + Z = y] ≤ e^{‖x - x'‖₁ / s} Pr[x' + Z = y]`. -/
theorem addNoise_le {s : ℝ} (hs : 0 < s) {n : ℕ} (x x' y : Fin n → ℤ) :
    addNoise (discreteLaplace s) x y
      ≤ ENNReal.ofReal (exp (l1 x x' / s)) * addNoise (discreteLaplace s) x' y := by
  simp only [addNoise_apply, iid_apply, discreteLaplace_apply hs]
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => mass_nonneg hs _,
    ← ENNReal.ofReal_prod_of_nonneg fun i _ => mass_nonneg hs _,
    ← ENNReal.ofReal_mul (exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [l1, Finset.sum_div, exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => mass_nonneg hs _) fun i _ => ?_
  have := mass_shift_le hs ((y - x) i) ((y - x') i)
  simpa [abs_sub_comm] using this

/-- **The discrete Laplace mechanism** (`NoisePrivacyMap` for `ZExpFamily<1>`): if `x`, `x'` are
within L1 distance `d` and the privacy map's output `o` satisfies
`laplace_bound(d, s, o)`, then `x + Z` and `x' + Z` are within max-divergence `o`. -/
theorem laplace_mechanism {s d : ℝ} {o : Option ℝ} (hb : LaplaceBound d s o)
    {n : ℕ} (x x' : Fin n → ℤ) (hx : l1 x x' ≤ d) :
    MaxDivClose (addNoise (discreteLaplace s) x) (addNoise (discreteLaplace s) x') o := by
  rcases o with _ | o
  · trivial
  obtain ⟨-, ⟨rfl, rfl⟩ | ⟨hs, hdo⟩⟩ := hb
  · -- `d = 0`: the inputs are equal.
    have : x = x' := by
      funext i
      have h0 : ∀ j ∈ Finset.univ, 0 ≤ |((x j : ℝ) - x' j)| := fun j _ => abs_nonneg _
      have hi := (Finset.sum_eq_zero_iff_of_nonneg h0).mp
        (le_antisymm hx (Finset.sum_nonneg h0)) i (Finset.mem_univ i)
      exact_mod_cast sub_eq_zero.mp (abs_eq_zero.mp hi)
    subst this
    exact maxDivClose_of_pointwise fun y => by simp
  · refine maxDivClose_of_pointwise fun y => (addNoise_le hs x x' y).trans ?_
    gcongr
    exact (div_le_div_of_nonneg_right hx hs.le).trans hdo

end OpenDP.Laplace
