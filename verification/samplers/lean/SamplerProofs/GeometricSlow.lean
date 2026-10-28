/-
`sample_geometric_exp_slow` (`rust/src/traits/samplers/cks20/mod.rs`), on its extracted code: for
`x > 0`, it returns `m` with probability `(1 - e^{-x}) e^{-x m}`, within `epsSlow`.

The loop counts the successes of `sample_bernoulli_exp(x)` before its first failure. Each
iteration continues with probability `e^{-x} < 1`.
-/
import SamplerProofs.Exp

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

open Classical

/-- The results of the samplers that return a `UBig`. -/
abbrev ResU := core.result.Result ℕ error.Error

/-- The geometric distribution with ratio `r`, shifted to start at `k`: `m ≥ k` has probability
`(1 - r) r^{m - k}`. -/
noncomputable def geom (r : ℝ) (k : ℕ) : ResU → ℝ≥0∞
  | .Ok m => if k ≤ m then ENNReal.ofReal ((1 - r) * r ^ (m - k)) else 0
  | .Err _ => 0

theorem tsum_geom {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : ∑' b, geom r 0 b = 1 := by
  rw [tsum_res]
  simp only [geom, zero_le, ↓reduceIte, Nat.sub_zero, tsum_zero, add_zero]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (by linarith) (pow_nonneg h0 m))
    ((summable_geometric_of_lt_one h0 h1).mul_left _), tsum_mul_left,
    tsum_geometric_of_lt_one h0 h1, mul_inv_cancel₀ (by linarith), ENNReal.ofReal_one]

/-- The error of `sample_geometric_exp_slow(x)`, where `D` bounds the bit length of `x`'s
denominator. -/
noncomputable def epsSlow (x : ℝ) (D : ℕ) : ℝ≥0∞ :=
  epsExp D * (1 - ENNReal.ofReal (Real.exp (-x)))⁻¹

namespace Slow

variable (x : ℚ)

/-- The extracted loop body. -/
def body : Body (Tape × ℕ) ResU := fun p =>
  traits.samplers.cks20.sample_geometric_exp_slow_loop.body tapeSource x p.1 p.2

/-- What the iteration at `k` does with the result of `sample_bernoulli_exp`. -/
def out (k : ℕ) : ResB → ControlFlow ℕ ResU
  | .Ok true => .cont (k + 1)
  | .Ok false => .done (.Ok k)
  | .Err e => .done (.Err e)

theorem step_eq (k : ℕ) (t : Tape) :
    stepP (Equiv.refl _) (body x) k t =
      bindP (fun t => traits.samplers.cks20.sample_bernoulli_exp_with tapeSource t x)
        (fun r t' => ok (out k r, t')) t := by
  simp only [stepP, body, traits.samplers.cks20.sample_geometric_exp_slow_loop.body, bindP,
    dashu_ratio.rbig.RBig.Insts.CoreCloneClone.clone, bind_ok, Equiv.refl_symm,
    Equiv.refl_apply, Std.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨r, t'⟩
  rcases r with b | e
  · cases b <;> simp [core.result.Result.Insts.CoreOpsTry.branch, out,
      dashu_int.ubig.UBig.ONE, dashu_int.ubig.UBig.Insts.CoreOpsArithAddAssignUBig.add_assign]
  · simp [core.result.Result.Insts.CoreOpsTry.branch, out,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

theorem code_eq : (fun t => traits.samplers.cks20.sample_geometric_exp_slow tapeSource t x) =
    loopP (Equiv.refl _) (body x) 0 := by
  funext t
  simp only [traits.samplers.cks20.sample_geometric_exp_slow,
    traits.samplers.cks20.sample_geometric_exp_slow_loop, dashu_int.ubig.UBig.ZERO, bind_ok,
    loopP, Equiv.refl_symm, Equiv.refl_apply]
  rfl

/-- The distribution of an iteration if `sample_bernoulli_exp` were exact. -/
noncomputable def K' (k : ℕ) (c : ControlFlow ℕ ResU) : ℝ≥0∞ :=
  ∑' r, bern (Real.exp (-(x : ℝ))) r * (if c = out k r then 1 else 0)

variable {x}

theorem cont_mass (k : ℕ) : ∑' k', K' x k (.cont k') ≤ ENNReal.ofReal (Real.exp (-(x : ℝ))) := by
  rw [tsum_cont_eq]
  unfold K'
  rw [tsum_pushforward, tsum_resB]
  simp [out, bern, isCont]

theorem super (k : ℕ) (b : ResU) :
    ∑' c, K' x k c * contOr (geom (Real.exp (-(x : ℝ)))) c b ≤ geom (Real.exp (-(x : ℝ))) k b := by
  unfold K'
  rw [tsum_pushforward, tsum_resB]
  have hr0 := Real.exp_nonneg (-(x : ℝ))
  simp only [out, contOr, bern, zero_mul, tsum_zero, add_zero]
  rcases b with m | e
  · simp only [geom, core.result.Result.Ok.injEq]
    by_cases hkm : k + 1 ≤ m
    · have hk : k ≤ m := by omega
      have hne : m ≠ k := by omega
      simp only [hkm, hk, ↓reduceIte, hne, mul_zero, add_zero]
      rw [← ENNReal.ofReal_mul hr0]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      rw [show m - k = m - (k + 1) + 1 by omega, pow_succ]
      ring
    · simp only [hkm, ↓reduceIte, mul_zero, zero_add]
      by_cases hmk : m = k
      · subst hmk
        simp
      · have : ¬ k ≤ m := by omega
        simp [hmk, this]
  · simp [geom]

theorem hstep (hx : 0 ≤ x) {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size x.den ≤ D) (k : ℕ) :
    Approx (stepP (Equiv.refl _) (body x) k) (K' x k) (epsExp D + 0) := by
  have h := approx_bind (Exp.exp_approx hx hD1 hD) (fun r _ => approx_pure (out k r))
    (le_of_eq (tsum_bern (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ x := by exact_mod_cast hx
      linarith))))
  rw [show stepP (Equiv.refl _) (body x) k = _ from funext (step_eq x k)]
  exact h

/-- **`sample_geometric_exp_slow(x)` is geometric with ratio `e^{-x}`**, for `x > 0`, within
`epsSlow x D`, where `D ≥ 1` bounds the bit length of `x`'s denominator. -/
theorem slow_approx (hx : 0 < x) {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size x.den ≤ D) :
    Approx (fun t => traits.samplers.cks20.sample_geometric_exp_slow tapeSource t x)
      (geom (Real.exp (-(x : ℝ))) 0) (epsSlow x D) := by
  rw [code_eq]
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have h := approx_loop (e := Equiv.refl _) (body := body x) (K' := K' x)
    (target := geom (Real.exp (-(x : ℝ)))) (I := fun _ => True) (δ := epsExp D + 0)
    (q := ENNReal.ofReal (Real.exp (-(x : ℝ))))
    (fun k _ => hstep hx.le hD1 hD k) (fun _ _ _ _ => trivial) (fun k _ => cont_mass k)
    (ofReal_exp_lt_one hx') (fun k _ b => super k b) (s := 0) trivial
  simpa [epsSlow] using h

end Slow

end OpenDP.Samplers
