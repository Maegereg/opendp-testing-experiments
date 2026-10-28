/-
`sample_bernoulli_exp` (`rust/src/traits/samplers/cks20/mod.rs`), on its extracted code: for
`x ≥ 0`, it returns `true` with probability `e^{-x}`, within `epsExp D`.

While `x > 1` the loop draws `Bernoulli(e^{-1})` (`sample_bernoulli_exp1(1)`): on `true` it continues
with `x - 1`, on `false` it returns `false`. Once `x ≤ 1` it returns `sample_bernoulli_exp1(x)`.
Each iteration continues with probability at most `e^{-1}`, so the errors of the `exp1` calls add up
to at most `(eps1 1 + eps1 D) / (1 - e^{-1})` (`approx_loop`).
-/
import SamplerProofs.Exp1

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

open Classical

/-- `1` for an outcome that continues the loop, `0` for one that returns. -/
noncomputable def isCont {S B : Type} : ControlFlow S B → ℝ≥0∞
  | .cont _ => 1
  | .done _ => 0

/-- The probability that an iteration continues. -/
theorem tsum_cont_eq {S B : Type} (K : ControlFlow S B → ℝ≥0∞) :
    ∑' s', K (.cont s') = ∑' c, K c * isCont c := by
  rw [tsum_controlFlow]
  simp [isCont]

theorem tsum_ite_eq_left {α : Type} (μ : α → ℝ≥0∞) (b : α) :
    ∑' r, μ r * (if b = r then 1 else 0) = μ b := by
  rw [tsum_eq_single b]
  · simp
  · intro r hr; simp [Ne.symm hr]

theorem ofReal_exp_lt_one {y : ℝ} (hy : 0 < y) : ENNReal.ofReal (Real.exp (-y)) < 1 := by
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr ?_
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The error of `sample_bernoulli_exp` when the denominator of `x` has at most `D` bits. -/
noncomputable def epsExp (D : ℕ) : ℝ≥0∞ :=
  (eps1 1 + eps1 D) * (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹

theorem epsExp_mono {D D' : ℕ} (h : D ≤ D') : epsExp D ≤ epsExp D' := by
  unfold epsExp
  gcongr
  exact eps1_mono h

namespace Exp

/-- The extracted loop body. -/
def body : Body (Tape × ℚ) ResB := fun p =>
  traits.samplers.cks20.sample_bernoulli_exp_with_loop.body tapeSource p.1 p.2

variable (x : ℚ)

/-- The argument of the iteration's `sample_bernoulli_exp1` call. -/
def arg : ℚ := if 1 < x then 1 else x

/-- What the iteration does with the result of `sample_bernoulli_exp1`. -/
def out (r : ResB) : ControlFlow ℚ ResB :=
  if 1 < x then
    match r with
    | .Ok true => .cont (x - 1)
    | .Ok false => .done (.Ok false)
    | .Err e => .done (.Err e)
  else .done r

theorem step_eq (t : Tape) :
    stepP (Equiv.refl _) body x t =
      bindP (fun t => traits.samplers.cks20.sample_bernoulli_exp1 tapeSource t (arg x))
        (fun r t' => ok (out x r, t')) t := by
  simp only [stepP, body, traits.samplers.cks20.sample_bernoulli_exp_with_loop.body, bindP,
    dashu_ratio.rbig.RBig.ONE, core.cmp.PartialOrd.gt.trait_default,
    core.cmp.PartialOrd.gt.default, core.cmp.PartialOrd.gt_body,
    dashu_ratio.rbig.RBig.Insts.CoreCmpPartialOrdRBig.partial_cmp, core.convert.IntoFrom.into,
    dashu_ratio.rbig.RBig.Insts.CoreConvertFromI32.from, bind_ok, bind_tc_ok, Equiv.refl_symm,
    Equiv.refl_apply, Option.some.injEq]
  by_cases hx : 1 < x
  · simp only [arg, out, hx, ↓reduceIte, compare_gt_iff_gt, decide_true]
    simp only [show ((1#i32 : Std.I32).val : ℚ) = 1 by simp, Std.bind_assoc]
    congr 1
    funext p
    rcases p with ⟨r, t'⟩
    rcases r with b | e
    · cases b <;> simp [core.result.Result.Insts.CoreOpsTry.branch,
        dashu_ratio.rbig.RBig.Insts.CoreOpsArithSubAssignRBig.sub_assign]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [arg, out, hx, ↓reduceIte, compare_gt_iff_gt, decide_false, Bool.false_eq_true]
    simp only [Std.bind_assoc]
    congr 1
    funext p
    rcases p with ⟨r, t'⟩
    simp

theorem code_eq : (fun t => traits.samplers.cks20.sample_bernoulli_exp_with tapeSource t x) =
    loopP (Equiv.refl _) body x := by
  funext t
  rfl

/-- The distribution of an iteration if `sample_bernoulli_exp1` were exact. -/
noncomputable def K' (y : ℚ) (c : ControlFlow ℚ ResB) : ℝ≥0∞ :=
  ∑' r, bern (Real.exp (-(arg y : ℝ))) r * (if c = out y r then 1 else 0)

variable {x}

theorem arg_mem (h0 : 0 ≤ x) : 0 ≤ arg x ∧ arg x ≤ 1 := by
  unfold arg; split_ifs with h
  · norm_num
  · exact ⟨h0, not_lt.mp h⟩

theorem hstep {D : ℕ} (hD1 : 1 ≤ D) (h0 : 0 ≤ x) (hD : Nat.size x.den ≤ D) :
    Approx (stepP (Equiv.refl _) body x) (K' x) (eps1 D + 0) := by
  obtain ⟨ha0, ha1⟩ := arg_mem h0
  have hDa : Nat.size (arg x).den ≤ D := by
    unfold arg; split_ifs
    · simpa using hD1
    · exact hD
  have hb := Exp1.exp1_approx ha0 ha1 hDa
  have h := approx_bind hb (fun r _ => approx_pure (out x r))
    (le_of_eq (tsum_bern (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ arg x := by exact_mod_cast ha0
      linarith))))
  rw [show stepP (Equiv.refl _) body x = _ from funext (step_eq x)]
  exact h

theorem K'_cont {y y' : ℚ} (h : K' y (.cont y') ≠ 0) : 1 < y ∧ y' = y - 1 := by
  by_contra hne
  apply h
  refine ENNReal.tsum_eq_zero.mpr fun r => ?_
  unfold out
  by_cases hy : 1 < y
  · have : y' ≠ y - 1 := fun e => hne ⟨hy, e⟩
    rcases r with b | e
    · cases b <;> simp [hy, this]
    · simp [hy]
  · simp [hy]

theorem cont_mass (y : ℚ) : ∑' y', K' y (.cont y') ≤ ENNReal.ofReal (Real.exp (-1)) := by
  rw [tsum_cont_eq]
  unfold K'
  rw [tsum_pushforward, tsum_resB]
  by_cases hy : 1 < y
  · simp [out, arg, hy, bern, isCont]
  · simp [out, hy, isCont]

theorem super (y : ℚ) (b : ResB) :
    ∑' c, K' y c * contOr (fun y' : ℚ => bern (Real.exp (-(y' : ℝ)))) c b ≤
      bern (Real.exp (-(y : ℝ))) b := by
  unfold K'
  rw [tsum_pushforward]
  by_cases hy : 1 < y
  · have hy' : (1 : ℝ) < y := by exact_mod_cast hy
    have hc1 : Real.exp (-((y - 1 : ℚ) : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by push_cast; linarith)
    have ha1 : Real.exp (-((1 : ℚ) : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have hac : Real.exp (-((1 : ℚ) : ℝ)) * Real.exp (-((y - 1 : ℚ) : ℝ)) =
        Real.exp (-(y : ℝ)) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    rw [tsum_resB]
    simp only [out, arg, hy, ↓reduceIte, contOr, bern, zero_mul, tsum_zero, add_zero]
    rcases b with b | e
    · cases b
      · -- `false`: `e^{-1} (1 - e^{-(y-1)}) + (1 - e^{-1}) = 1 - e^{-y}`.
        simp only [↓reduceIte, mul_one]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
          ← ENNReal.ofReal_add (mul_nonneg (Real.exp_nonneg _) (by linarith)) (by linarith)]
        refine le_of_eq (congrArg ENNReal.ofReal ?_)
        rw [← hac]; ring
      · simp only [↓reduceIte, core.result.Result.Ok.injEq, mul_zero, add_zero,
          Bool.true_eq_false, ↓reduceIte]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), hac]
    · simp
  · simp only [out, arg, hy, ↓reduceIte, contOr]
    rw [tsum_ite_eq_left]

/-- **`sample_bernoulli_exp(x)` returns `true` with probability `e^{-x}`**, for `x ≥ 0`, within
`epsExp D`, where `D ≥ 1` bounds the bit length of `x`'s denominator. -/
theorem exp_approx (h0 : 0 ≤ x) {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size x.den ≤ D) :
    Approx (fun t => traits.samplers.cks20.sample_bernoulli_exp_with tapeSource t x)
      (bern (Real.exp (-(x : ℝ)))) (epsExp D) := by
  rw [code_eq]
  have hq1 := ofReal_exp_lt_one (show (0 : ℝ) < 1 by norm_num)
  have h := approx_loop (e := Equiv.refl _) (body := body) (K' := K')
    (target := fun y : ℚ => bern (Real.exp (-(y : ℝ))))
    (I := fun y => 0 ≤ y ∧ Nat.size y.den ≤ D) (δ := eps1 D + 0)
    (q := ENNReal.ofReal (Real.exp (-1)))
    (fun y hy => by
      have := hstep hD1 hy.1 hy.2
      exact this.congr fun t => rfl)
    (fun y hy y' h => by
      obtain ⟨hlt, rfl⟩ := K'_cont h
      refine ⟨by linarith, ?_⟩
      have : (y - 1).den = y.den := by
        simp
      rw [this]; exact hy.2)
    (fun y _ => cont_mass y) (by simp) (fun y _ b => super y b) ⟨h0, hD⟩
  refine h.mono (fun _ => le_rfl) ?_
  unfold epsExp
  exact mul_le_mul' (by rw [add_zero]; exact le_add_self) le_rfl

end Exp

end OpenDP.Samplers
