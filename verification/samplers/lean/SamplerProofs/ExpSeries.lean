/-
The series behind `sample_bernoulli_exp1`: with `a i = x^i / i!`,
`∑_{i even} (a i - a (i+1)) = e^{-x}` and `∑_{i odd} (a i - a (i+1)) = 1 - e^{-x}`.
-/
import Mathlib

open Nat

namespace OpenDP.Samplers

/-- `x^i / i!`. -/
noncomputable def expTerm (x : ℝ) (i : ℕ) : ℝ := x ^ i / i !

theorem hasSum_exp_neg (x : ℝ) : HasSum (fun n => (-x) ^ n / n !) (Real.exp (-x)) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp (-x)

/-- Pairing consecutive terms of a summable real series. -/
theorem hasSum_pairs {g : ℕ → ℝ} {E : ℝ} (hg : HasSum g E) :
    HasSum (fun m => g (2 * m) + g (2 * m + 1)) E := by
  have he := (hg.summable.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))).hasSum
  have ho := (hg.summable.comp_injective
    ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))).hasSum
  have := hg.unique (he.even_add_odd ho)
  rw [this]
  exact he.add ho

theorem neg_pow_div_even (x : ℝ) (m : ℕ) :
    (-x) ^ (2 * m) / (2 * m)! + (-x) ^ (2 * m + 1) / (2 * m + 1)! =
      expTerm x (2 * m) - expTerm x (2 * m + 1) := by
  rw [expTerm, expTerm, Even.neg_pow ⟨m, by ring⟩, Odd.neg_pow ⟨m, rfl⟩, neg_div]
  ring

/-- The terms of the even series. -/
noncomputable def evenTerm (x : ℝ) (i : ℕ) : ℝ :=
  if i % 2 = 0 then expTerm x i - expTerm x (i + 1) else 0

/-- The terms of the odd series. -/
noncomputable def oddTerm (x : ℝ) (i : ℕ) : ℝ :=
  if i % 2 = 1 then expTerm x i - expTerm x (i + 1) else 0

theorem hasSum_exp_even (x : ℝ) : HasSum (evenTerm x) (Real.exp (-x)) := by
  have h := hasSum_pairs (hasSum_exp_neg x)
  simp_rw [neg_pow_div_even] at h
  have he : HasSum (fun m => evenTerm x (2 * m)) (Real.exp (-x)) := by
    refine h.congr_fun fun m => ?_
    simp [evenTerm, Nat.mul_mod_right]
  have ho : HasSum (fun m => evenTerm x (2 * m + 1)) 0 := by
    refine (hasSum_zero (α := ℝ)).congr_fun fun m => ?_
    simp [evenTerm, Nat.add_mod]
  simpa using HasSum.even_add_odd (f := evenTerm x) he ho

theorem hasSum_exp_odd (x : ℝ) : HasSum (oddTerm x) (1 - Real.exp (-x)) := by
  -- The tail `∑_{n ≥ 1} (-x)^n / n!` is `e^{-x} - 1`.
  have htail : HasSum (fun n => (-x) ^ (n + 1) / (n + 1)!) (Real.exp (-x) - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr (hasSum_exp_neg x)
    simpa using this
  have h := (hasSum_pairs htail).neg
  have ho : HasSum (fun m => oddTerm x (2 * m + 1)) (1 - Real.exp (-x)) := by
    rw [show 1 - Real.exp (-x) = -(Real.exp (-x) - 1) by ring]
    refine h.congr_fun fun m => ?_
    simp only [oddTerm, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.one_mod, ↓reduceIte]
    rw [expTerm, expTerm, Odd.neg_pow ⟨m, rfl⟩, Even.neg_pow ⟨m + 1, by ring⟩, neg_div]
    ring_nf
  have he : HasSum (fun m => oddTerm x (2 * m)) 0 := by
    refine (hasSum_zero (α := ℝ)).congr_fun fun m => ?_
    simp [oddTerm, Nat.mul_mod_right]
  simpa using HasSum.even_add_odd (f := oddTerm x) he ho

theorem expTerm_nonneg {x : ℝ} (h0 : 0 ≤ x) (i : ℕ) : 0 ≤ expTerm x i :=
  div_nonneg (pow_nonneg h0 i) (by positivity)

/-- `a (i+1) = a i · x / (i+1)`. -/
theorem expTerm_succ (x : ℝ) (i : ℕ) : expTerm x (i + 1) = expTerm x i * (x / (i + 1)) := by
  rw [expTerm, expTerm, pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

theorem expTerm_sub_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (i : ℕ) :
    0 ≤ expTerm x i - expTerm x (i + 1) := by
  rw [expTerm_succ, sub_nonneg]
  refine mul_le_of_le_one_right (expTerm_nonneg h0 i) ?_
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

end OpenDP.Samplers
