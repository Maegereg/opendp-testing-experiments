/-
The identity behind `sample_geometric_exp_fast` (CKS20, Algorithm 2).

With `ρ = e^{-1/d}`: the loop accepts `u < d` with probability `ρ^u`, and then returns
`⌊(v d + u) / n⌋` for `v` geometric with ratio `e^{-1} = ρ^d`. Writing `X = v d + u`, `X` has weight
`(1 - ρ^d) ρ^X`, and `⌊X / n⌋ = y` for `X = y n + j`, `j < n`. Hence, averaged over the uniform
`u`, the loop returns `y` with probability `A y = (1 - ρ^n) ρ^{n y}`: geometric with ratio
`e^{-n/d}` (`average`).
-/
import SamplerProofs.GeometricSlow

open scoped ENNReal

namespace OpenDP.Samplers.FastMath

open Classical Finset

variable (n d : ℕ)

/-- The acceptance probability of `u`: `e^{-u/d}`. -/
noncomputable def pacc (u : ℕ) : ℝ := Real.exp (-((u : ℝ) / d))

/-- The weights of `sample_geometric_exp_slow(1)`: `(1 - e^{-1}) e^{-v}`. -/
noncomputable def gw (v : ℕ) : ℝ := (1 - Real.exp (-1)) * Real.exp (-1) ^ v

/-- The geometric distribution with ratio `e^{-n/d}`. -/
noncomputable def A (y : ℕ) : ℝ := (1 - Real.exp (-((n : ℝ) / d))) * Real.exp (-((n : ℝ) / d)) ^ y

/-- Accepting `u`, the probability of returning `y`. -/
noncomputable def G (u y : ℕ) : ℝ≥0∞ :=
  ∑' v, ENNReal.ofReal (gw v) * (if y = (v * d + u) / n then 1 else 0)

/-- From `u`, the loop returns `y` with probability `tgt u (.Ok y)`. -/
noncomputable def tgt (u : ℕ) : ResU → ℝ≥0∞
  | .Ok y => ENNReal.ofReal (pacc d u) * G n d u y +
      ENNReal.ofReal (1 - pacc d u) * ENNReal.ofReal (A n d y)
  | .Err _ => 0

variable {n d}

/-- `ρ = e^{-1/d}`. -/
noncomputable def ρ (d : ℕ) : ℝ := Real.exp (-(1 / (d : ℝ)))

theorem ρ_pow (hd : 0 < d) (a : ℝ) (k : ℕ) (h : a = k / d) : Real.exp (-a) = ρ d ^ k := by
  rw [ρ, ← Real.exp_nat_mul, h]
  congr 1
  field_simp

theorem pacc_eq (hd : 0 < d) (u : ℕ) : pacc d u = ρ d ^ u := ρ_pow hd _ u rfl

theorem exp_neg_one_eq (hd : 0 < d) : Real.exp (-1) = ρ d ^ d :=
  ρ_pow hd 1 d (by field_simp)

theorem exp_neg_nd_eq (hd : 0 < d) : Real.exp (-((n : ℝ) / d)) = ρ d ^ n := ρ_pow hd _ n rfl

theorem ρ_nonneg : 0 ≤ ρ d := Real.exp_nonneg _

theorem pacc_mem (u : ℕ) : 0 ≤ pacc d u ∧ pacc d u ≤ 1 := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
  have : (0 : ℝ) ≤ u / d := by positivity
  linarith

theorem ρ_le_one : ρ d ≤ 1 := by
  refine Real.exp_le_one_iff.mpr ?_
  have : (0 : ℝ) ≤ 1 / d := by positivity
  linarith

theorem A_nonneg (hd : 0 < d) (y : ℕ) : 0 ≤ A n d y := by
  refine mul_nonneg ?_ (pow_nonneg (Real.exp_nonneg _) y)
  rw [exp_neg_nd_eq hd]
  linarith [pow_le_one₀ (ρ_nonneg (d := d)) (ρ_le_one (d := d)) (n := n)]

/-- `(1 - ρ^d) ∑_{j<n} ρ^j = (1 - ρ^n) ∑_{u<d} ρ^u`. -/
theorem geom_identity (r : ℝ) :
    (1 - r ^ d) * ∑ j ∈ range n, r ^ j = (1 - r ^ n) * ∑ u ∈ range d, r ^ u := by
  have h1 := geom_sum_mul r n
  have h2 := geom_sum_mul r d
  have e1 : 1 - r ^ n = (∑ j ∈ range n, r ^ j) * (1 - r) := by linarith
  have e2 : 1 - r ^ d = (∑ u ∈ range d, r ^ u) * (1 - r) := by linarith
  rw [e1, e2]
  ring

/-- Summing over `X` is summing over `(v, u)` with `X = v d + u`, `u < d`. -/
theorem tsum_divMod (hd : 0 < d) (H : ℕ → ℝ≥0∞) :
    ∑' X, H X = ∑ u ∈ range d, ∑' v, H (v * d + u) := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [← (Nat.divModEquiv d).symm.tsum_eq, ENNReal.tsum_prod']
  simp only [Nat.divModEquiv, Equiv.coe_fn_symm_mk]
  simp_rw [tsum_fintype]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun v => ?_
  exact Fin.sum_univ_eq_sum_range (fun u => H (v * d + u)) d

/-- The key identity: `∑_{u<d} e^{-u/d} G u y = A y ∑_{u<d} e^{-u/d}`. -/
theorem key (hn : 0 < n) (hd : 0 < d) (y : ℕ) :
    ∑ u ∈ range d, ENNReal.ofReal (pacc d u) * G n d u y =
      ENNReal.ofReal (A n d y) * ∑ u ∈ range d, ENNReal.ofReal (pacc d u) := by
  have hρ0 := ρ_nonneg (d := d)
  -- Both sides as sums over `X`.
  let H : ℕ → ℝ≥0∞ := fun X =>
    ENNReal.ofReal ((1 - Real.exp (-1)) * ρ d ^ X) * (if y = X / n then 1 else 0)
  have hc : 0 ≤ 1 - Real.exp (-1) := by
    linarith [Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)]
  have hL : ∑ u ∈ range d, ENNReal.ofReal (pacc d u) * G n d u y = ∑' X, H X := by
    rw [tsum_divMod hd]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [G, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun v => ?_
    simp only [H]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (pacc_mem u).1]
    congr 2
    rw [pacc_eq hd, gw, exp_neg_one_eq hd, pow_add, ← pow_mul]
    ring
  -- Summing over `X = y' n + j`: only `y' = y` contributes.
  have hR : ∑' X, H X = ∑ j ∈ range n,
      ENNReal.ofReal ((1 - Real.exp (-1)) * ρ d ^ (y * n + j)) := by
    rw [tsum_divMod hn]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [tsum_eq_single y]
    · simp only [H]
      rw [show (y * n + j) / n = y by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt (mem_range.mp hj),
          Nat.zero_add]]
      simp
    · intro y' hy'
      simp only [H]
      rw [show (y' * n + j) / n = y' by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt (mem_range.mp hj),
          Nat.zero_add]]
      simp [Ne.symm hy']
  rw [hL, hR, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg hc (pow_nonneg hρ0 _)),
    ← ENNReal.ofReal_sum_of_nonneg (fun u _ => (pacc_mem u).1),
    ← ENNReal.ofReal_mul (A_nonneg hd y)]
  congr 1
  simp_rw [pacc_eq hd, A, exp_neg_nd_eq hd, exp_neg_one_eq hd, pow_add, ← Finset.mul_sum]
  rw [← pow_mul]
  have := geom_identity (n := n) (d := d) (ρ d)
  calc (1 - ρ d ^ d) * (ρ d ^ (y * n) * ∑ j ∈ range n, ρ d ^ j)
      = ρ d ^ (y * n) * ((1 - ρ d ^ d) * ∑ j ∈ range n, ρ d ^ j) := by ring
    _ = ρ d ^ (y * n) * ((1 - ρ d ^ n) * ∑ u ∈ range d, ρ d ^ u) := by rw [this]
    _ = _ := by rw [mul_comm n y]; ring

/-- **Averaged over the uniform `u < d`, the loop returns `y` with probability `A y`.** -/
theorem average (hn : 0 < n) (hd : 0 < d) (y : ℕ) :
    ∑ u ∈ range d, (d : ℝ≥0∞)⁻¹ * tgt n d u (.Ok y) = ENNReal.ofReal (A n d y) := by
  rw [← Finset.mul_sum]
  simp only [tgt]
  rw [Finset.sum_add_distrib, key hn hd, ← Finset.sum_mul, mul_comm _ (ENNReal.ofReal (A n d y)),
    ← mul_add, ← Finset.sum_add_distrib]
  have hone : ∀ u ∈ range d, ENNReal.ofReal (pacc d u) + ENNReal.ofReal (1 - pacc d u) = 1 := by
    intro u _
    rw [← ENNReal.ofReal_add (pacc_mem u).1 (by linarith [(pacc_mem (d := d) u).2])]
    simp
  rw [Finset.sum_congr rfl hone, Finset.sum_const, card_range, nsmul_eq_mul, mul_one,
    mul_comm, mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hd.ne') (by simp), mul_one]

end OpenDP.Samplers.FastMath
