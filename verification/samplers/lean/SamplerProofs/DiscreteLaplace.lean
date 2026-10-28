/-
`sample_discrete_laplace` (`rust/src/traits/samplers/cks20/mod.rs`), on its extracted code: for
`scale > 0`, it returns `z` with probability `(1 - r) / (1 + r) r^{|z|}`, `r = e^{-1/scale}`
(the discrete Laplace distribution of `ZExpFamily<1>`'s Proof Definition), within
`2 epsFast D`; for `scale = 0` it returns `0`.

The loop draws a sign (`sample_standard_bernoulli`) and a magnitude `m`
(`sample_geometric_exp_fast(1/scale)`, geometric with ratio `r`), and retries on "negative zero".
Each iteration continues with probability `(1 - r) / 2 ≤ 1/2`.
-/
import SamplerProofs.GeometricFast

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

open Classical

/-- The results of the samplers that return an `IBig`. -/
abbrev ResI := core.result.Result ℤ error.Error

/-- The discrete Laplace distribution with ratio `r = e^{-1/scale}`. -/
noncomputable def lap (r : ℝ) : ResI → ℝ≥0∞
  | .Ok z => ENNReal.ofReal ((1 - r) / (1 + r) * r ^ z.natAbs)
  | .Err _ => 0

theorem hasSum_pow_natAbs {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    HasSum (fun z : ℤ => r ^ z.natAbs) ((1 + r) / (1 - r)) := by
  have hg := hasSum_geometric_of_lt_one h0 h1
  have hpos : HasSum (fun n : ℕ => r ^ (n : ℤ).natAbs) (1 - r)⁻¹ :=
    hg.congr_fun fun n => by simp
  have hneg : HasSum (fun n : ℕ => r ^ (-(n + 1 : ℤ)).natAbs) (r * (1 - r)⁻¹) := by
    refine (hg.mul_left r).congr_fun fun n => ?_
    rw [← pow_succ', show (-(n + 1 : ℤ)).natAbs = n + 1 by omega]
  have h := HasSum.of_nat_of_neg_add_one (f := fun z : ℤ => r ^ z.natAbs) hpos hneg
  rwa [show (1 - r)⁻¹ + r * (1 - r)⁻¹ = (1 + r) / (1 - r) by
    field_simp [(sub_pos.mpr h1).ne']] at h

theorem tsum_lap {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : ∑' b, lap r b = 1 := by
  rw [tsum_res]
  simp only [lap, tsum_zero, add_zero]
  have hc : 0 ≤ (1 - r) / (1 + r) := div_nonneg (by linarith) (by linarith)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => mul_nonneg hc (pow_nonneg h0 _))
    ((hasSum_pow_natAbs h0 h1).summable.mul_left _), tsum_mul_left,
    (hasSum_pow_natAbs h0 h1).tsum_eq]
  rw [show (1 - r) / (1 + r) * ((1 + r) / (1 - r)) = 1 by
    field_simp [(sub_pos.mpr h1).ne', (show (0 : ℝ) < 1 + r by linarith).ne']]
  simp

namespace Lap

variable (inv : ℚ)

/-- The state of the loop is the tape alone. -/
def e : Tape ≃ Tape × PUnit := (Equiv.prodPUnit Tape).symm

/-- The extracted loop body. -/
def body : Body Tape ResI := fun t =>
  traits.samplers.cks20.sample_discrete_laplace_with_loop.body tapeSource inv t

/-- What the iteration returns, given the sign and the magnitude. -/
def out (pos : Bool) : ResU → ControlFlow PUnit ResI
  | .Ok m => if pos then .done (.Ok m) else if m = 0 then .cont () else .done (.Ok (-(m : ℤ)))
  | .Err e => .done (.Err e)

/-- The iteration after drawing the sign. -/
def cont : ResB → Prog (ControlFlow PUnit ResI)
  | .Ok pos => bindP (fun t => traits.samplers.cks20.sample_geometric_exp_fast_with tapeSource t inv)
      (fun r t => ok (out pos r, t))
  | .Err e => fun t => ok (.done (.Err e), t)

theorem step_eq (t : Tape) :
    stepP e (body inv) () t =
      bindP (fun t => traits.samplers.bernoulli.sample_standard_bernoulli_with tapeSource t)
        (cont inv) t := by
  simp only [stepP, body, e, traits.samplers.cks20.sample_discrete_laplace_with_loop.body, bindP,
    Equiv.symm_symm, Equiv.prodPUnit_apply, Std.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨r, t'⟩
  rcases r with pos | err
  · simp [core.result.Result.Insts.CoreOpsTry.branch, cont, bindP,
      dashu_ratio.rbig.RBig.Insts.CoreCloneClone.clone]
    congr 1
    funext q
    rcases q with ⟨r2, t2⟩
    rcases r2 with m | err
    · cases pos <;> by_cases hm : m = 0 <;>
        simp [out, dashu_int.convert.UBig.as_ibig,
          dashu_int.ibig.IBig.Insts.CoreCloneClone.clone, dashu_int.ibig.IBig.is_zero, hm,
          dashu_int.ibig.IBig.Insts.CoreOpsArithNegIBig.neg]
    · simp [out,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch, cont,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The targets of the continuations. -/
noncomputable def nu (r : ℝ) : ResB → ControlFlow PUnit ResI → ℝ≥0∞
  | .Ok pos => fun c => ∑' m, geom r 0 m * (if c = out pos m then 1 else 0)
  | .Err e => fun c => if c = .done (.Err e) then 1 else 0

/-- The distribution of an iteration if the samplers it calls were exact. -/
noncomputable def K' (r : ℝ) (_ : PUnit) (c : ControlFlow PUnit ResI) : ℝ≥0∞ :=
  ∑' b, bern (1 / 2) b * nu r b c

variable {inv}

theorem hstep (hinv : 0 < inv) (hs : Nat.size inv.den < bitBound) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : Nat.size inv.den ≤ D) :
    Approx (stepP e (body inv) ()) (K' (Real.exp (-(inv : ℝ))) ()) (0 + epsFast D) := by
  have hb := Approx.of_hasDist standard_bernoulli_dist
    (le_of_eq (tsum_bern (by norm_num) (by norm_num)).symm)
  have h := approx_bind hb (k := cont inv) (ν := nu (Real.exp (-(inv : ℝ)))) (ε₂ := epsFast D)
    (fun b _ => by
      rcases b with pos | err
      · have := approx_bind (Fast.fast_approx hinv hs hD1 hD)
          (fun m _ => approx_pure (out pos m))
          (le_of_eq (tsum_geom (Real.exp_nonneg _) (by
            rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
              have : (0 : ℝ) < inv := by exact_mod_cast hinv
              linarith))))
        exact this.mono (fun _ => le_rfl) (by simp)
      · exact (approx_pure _).mono (fun _ => le_rfl) (by simp))
    (le_of_eq (tsum_bern (by norm_num) (by norm_num)))
  rw [show stepP e (body inv) () = _ from funext (step_eq inv)]
  exact h

/-- Sums against the continuations' targets. -/
theorem tsum_nu (r : ℝ) (b : ResB) (M : ControlFlow PUnit ResI → ℝ≥0∞) :
    ∑' c, nu r b c * M c =
      match b with
      | .Ok pos => ∑' m, geom r 0 m * M (out pos m)
      | .Err e => M (.done (.Err e)) := by
  rcases b with pos | err
  · exact tsum_pushforward _ _ M
  · simp only [nu]
    rw [tsum_eq_single (.done (.Err err))]
    · simp
    · intro c hc; simp [hc]

theorem K'_sum (r : ℝ) (M : ControlFlow PUnit ResI → ℝ≥0∞) :
    ∑' c, K' r () c * M c = ENNReal.ofReal (1 / 2) * ∑' m, geom r 0 m * M (out true m) +
      ENNReal.ofReal (1 / 2) * ∑' m, geom r 0 m * M (out false m) := by
  unfold K'
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left, tsum_nu]
  rw [tsum_resB]
  simp only [bern, zero_mul, tsum_zero, add_zero, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]

theorem cont_mass {r : ℝ} (h0 : 0 ≤ r) :
    ∑' u, K' r () (.cont u) ≤ ENNReal.ofReal (1 / 2) := by
  rw [tsum_cont_eq, K'_sum]
  -- Only "negative zero" continues.
  have hT : ∑' m, geom r 0 m * isCont (out true m) = 0 := by
    refine ENNReal.tsum_eq_zero.mpr fun m => ?_
    rcases m with m | e <;> simp [out, isCont]
  have hF : ∑' m, geom r 0 m * isCont (out false m) = geom r 0 (.Ok 0) := by
    rw [tsum_res, tsum_eq_single 0]
    · simp [out, isCont, geom]
    · intro m hm; simp [out, isCont, hm]
  rw [hT, hF]
  simp only [geom, le_refl, ↓reduceIte, Nat.sub_zero, pow_zero, mul_one, mul_zero, zero_add]
  calc ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 - r) ≤ ENNReal.ofReal (1 / 2) * 1 := by
        gcongr; rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = _ := mul_one _

theorem contOr_out_true (L : ResI → ℝ≥0∞) (m : ℕ) (b : ResI) :
    contOr (fun _ : PUnit => L) (out true (.Ok m)) b = if b = .Ok (m : ℤ) then 1 else 0 := rfl

theorem contOr_out_false (L : ResI → ℝ≥0∞) (m : ℕ) (b : ResI) :
    contOr (fun _ : PUnit => L) (out false (.Ok m)) b =
      if m = 0 then L b else if b = .Ok (-(m : ℤ)) then 1 else 0 := by
  by_cases hm : m = 0 <;> simp [out, contOr, hm]

theorem contOr_out_err (L : ResI → ℝ≥0∞) (pos : Bool) (e : error.Error) (b : ResI) :
    contOr (fun _ : PUnit => L) (out pos (.Err e)) b = if b = .Err e then 1 else 0 := rfl

theorem super {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (b : ResI) :
    ∑' c, K' r () c * contOr (fun _ : PUnit => lap r) c b ≤ lap r b := by
  rw [K'_sum, tsum_res, tsum_res]
  simp only [contOr_out_true, contOr_out_false, contOr_out_err, geom, zero_le, ↓reduceIte,
    Nat.sub_zero, zero_mul, tsum_zero, add_zero]
  rcases b with z | err
  · -- Both signs: `m = |z|` (and `m = 0` retries).
    have hpos : ∑' m : ℕ, ENNReal.ofReal ((1 - r) * r ^ m) *
        (if (core.result.Result.Ok z : ResI) = .Ok (m : ℤ) then 1 else 0) =
        if 0 ≤ z then ENNReal.ofReal ((1 - r) * r ^ z.natAbs) else 0 := by
      by_cases hz : 0 ≤ z
      · rw [tsum_eq_single z.natAbs]
        · simp [hz, Int.natAbs_of_nonneg hz]
        · intro m hm
          have : z ≠ (m : ℤ) := by omega
          simp [this]
      · simp only [hz, ↓reduceIte]
        refine ENNReal.tsum_eq_zero.mpr fun m => ?_
        have : z ≠ (m : ℤ) := by omega
        simp [this]
    have hneg : ∑' m : ℕ, ENNReal.ofReal ((1 - r) * r ^ m) *
        (if m = 0 then lap r (.Ok z)
          else if (core.result.Result.Ok z : ResI) = .Ok (-(m : ℤ)) then 1 else 0) =
        ENNReal.ofReal (1 - r) * lap r (.Ok z) +
          if z < 0 then ENNReal.ofReal ((1 - r) * r ^ z.natAbs) else 0 := by
      rw [tsum_eq_zero_add' ENNReal.summable]
      simp only [↓reduceIte, pow_zero, mul_one, Nat.add_one_ne_zero]
      congr 1
      by_cases hz : z < 0
      · simp only [hz, ↓reduceIte]
        rw [tsum_eq_single (z.natAbs - 1)]
        · have hz2 : z = -((z.natAbs - 1 + 1 : ℕ) : ℤ) := by omega
          simp only [core.result.Result.Ok.injEq, show z.natAbs - 1 + 1 = z.natAbs by omega,
            show (z = -(z.natAbs : ℤ)) = True from eq_true (by omega), ↓reduceIte, mul_one]
        · intro m hm
          have : ¬ z = -((m + 1 : ℕ) : ℤ) := by omega
          simp only [core.result.Result.Ok.injEq, this, ↓reduceIte, mul_zero]
      · simp only [hz, ↓reduceIte]
        refine ENNReal.tsum_eq_zero.mpr fun m => ?_
        have : ¬ z = -((m + 1 : ℕ) : ℤ) := by omega
        simp only [core.result.Result.Ok.injEq, this, ↓reduceIte, mul_zero]
    rw [hpos, hneg]
    -- `½ (1-r) r^|z| + ½ (1-r) L(z) = L(z)`.
    have hL : lap r (.Ok z) = ENNReal.ofReal ((1 - r) / (1 + r) * r ^ z.natAbs) := rfl
    have hc : 0 ≤ (1 - r) / (1 + r) := div_nonneg (by linarith) (by linarith)
    have hs := pow_nonneg h0 z.natAbs
    have key : (1 / 2 : ℝ) * ((1 - r) * r ^ z.natAbs) +
        1 / 2 * ((1 - r) * ((1 - r) / (1 + r) * r ^ z.natAbs)) =
        (1 - r) / (1 + r) * r ^ z.natAbs := by
      field_simp
      ring
    have h1' : 0 ≤ 1 - r := by linarith
    have e1 : ENNReal.ofReal (1 - r) * ENNReal.ofReal ((1 - r) / (1 + r) * r ^ z.natAbs) =
        ENNReal.ofReal ((1 - r) * ((1 - r) / (1 + r) * r ^ z.natAbs)) :=
      (ENNReal.ofReal_mul h1').symm
    have comb : ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((1 - r) * r ^ z.natAbs) +
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal ((1 - r) * ((1 - r) / (1 + r) * r ^ z.natAbs)) =
        ENNReal.ofReal ((1 - r) / (1 + r) * r ^ z.natAbs) := by
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity), key]
    rw [hL]
    by_cases hz : 0 ≤ z
    · have hz' : ¬ z < 0 := not_lt.mpr hz
      simp only [hz, hz', ↓reduceIte, add_zero, e1]
      exact le_of_eq comb
    · have hz' : z < 0 := lt_of_not_ge hz
      simp only [hz, hz', ↓reduceIte, zero_add, e1, mul_zero]
      rw [mul_add, add_comm]
      exact le_of_eq comb
  · simp [lap]

/-- The code: `0` for `scale = 0`, otherwise the loop with `inv = 1 / scale`. -/
theorem code_eq {s : ℚ} (hs : s ≠ 0) (t : Tape) :
    traits.samplers.cks20.sample_discrete_laplace_with tapeSource t s =
      loopP e (body ((s.den : ℚ) / |(s.num : ℚ)|)) () t := by
  simp [traits.samplers.cks20.sample_discrete_laplace_with, dashu_ratio.rbig.RBig.is_zero, hs,
    dashu_ratio.rbig.RBig.into_parts, dashu_int.convert.UBig.as_ibig,
    dashu_int.ibig.IBig.Insts.CoreCloneClone.clone, dashu_int.ibig.IBig.into_parts,
    dashu_ratio.rbig.RBig.from_parts]
  rfl

end Lap

/-- The error of `sample_discrete_laplace(scale)`, where `D` bounds the bit length of `scale`'s
numerator. -/
noncomputable def epsLap (D : ℕ) : ℝ≥0∞ := (0 + epsFast D) * (1 - ENNReal.ofReal (1 / 2))⁻¹

/-- **`sample_discrete_laplace(scale)` is discrete Laplace with ratio `e^{-1/scale}`**, for
`scale > 0` whose numerator's bit length fits in a `usize`, within `epsLap D` (`D ≥ 1` bounds that
bit length). -/
theorem discrete_laplace_approx {s : ℚ} (hs : 0 < s) (hsz : Nat.size s.num.natAbs < bitBound)
    {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size s.num.natAbs ≤ D) :
    Approx (fun t => traits.samplers.cks20.sample_discrete_laplace_with tapeSource t s)
      (lap (Real.exp (-(1 / (s : ℝ))))) (epsLap D) := by
  have hinv : (s.den : ℚ) / |(s.num : ℚ)| = s⁻¹ := by
    rw [abs_of_pos (by exact_mod_cast Rat.num_pos.mpr hs)]
    conv_rhs => rw [← Rat.num_div_den s]
    rw [inv_div]
  have hipos : 0 < s⁻¹ := inv_pos.mpr hs
  have hden : (s⁻¹).den = s.num.natAbs := Rat.den_inv_of_ne_zero hs.ne'
  rw [show (fun t => traits.samplers.cks20.sample_discrete_laplace_with tapeSource t s) = _ from
    funext (Lap.code_eq hs.ne'), hinv]
  have hr0 := Real.exp_nonneg (-((s⁻¹ : ℚ) : ℝ))
  have hr1 : Real.exp (-((s⁻¹ : ℚ) : ℝ)) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
      have : (0 : ℝ) < (s⁻¹ : ℚ) := by exact_mod_cast hipos
      linarith)
  have hq : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have h := approx_loop (e := Lap.e) (body := Lap.body s⁻¹)
    (K' := Lap.K' (Real.exp (-((s⁻¹ : ℚ) : ℝ))))
    (target := fun _ => lap (Real.exp (-((s⁻¹ : ℚ) : ℝ)))) (I := fun _ => True)
    (δ := 0 + epsFast D) (q := ENNReal.ofReal (1 / 2))
    (fun _ _ => Lap.hstep hipos (hden ▸ hsz) hD1 (hden ▸ hD))
    (fun _ _ _ _ => trivial) (fun _ _ => Lap.cont_mass hr0)
    hq (fun _ _ b => Lap.super hr0 hr1 b) (s := ()) trivial
  have hcast : ((s⁻¹ : ℚ) : ℝ) = 1 / (s : ℝ) := by push_cast; ring
  rw [hcast] at h
  exact h

/-- With `scale = 0` the sampler returns `0`. -/
theorem discrete_laplace_zero :
    HasDist (fun t => traits.samplers.cks20.sample_discrete_laplace_with tapeSource t 0)
      (fun b => if b = .Ok 0 then 1 else 0) := by
  have e : (fun t => traits.samplers.cks20.sample_discrete_laplace_with tapeSource t 0) =
      fun t => ok (.Ok 0, t) := by
    funext t
    simp [traits.samplers.cks20.sample_discrete_laplace_with, dashu_ratio.rbig.RBig.is_zero,
      core.convert.IntoFrom.into, dashu_int.ibig.IBig.Insts.CoreConvertFromI32.from]
  rw [e]
  exact hasDist_pure (.Ok 0 : ResI)

/-- **The probability that `sample_discrete_laplace(scale)` returns `z` is within `epsLap D` of
the discrete Laplace mass** `(1 - r) / (1 + r) r^{|z|}`, `r = e^{-1/scale}`, and never above it. -/
theorem discrete_laplace_close {s : ℚ} (hs : 0 < s) (hsz : Nat.size s.num.natAbs < bitBound)
    {D : ℕ} (hD1 : 1 ≤ D) (hD : Nat.size s.num.natAbs ≤ D) (z : ℤ) :
    let r := Real.exp (-(1 / (s : ℝ)))
    mass (fun t => traits.samplers.cks20.sample_discrete_laplace_with tapeSource t s) (.Ok z) ≤
        ENNReal.ofReal ((1 - r) / (1 + r) * r ^ z.natAbs) ∧
      ENNReal.ofReal ((1 - r) / (1 + r) * r ^ z.natAbs) ≤
        mass (fun t => traits.samplers.cks20.sample_discrete_laplace_with tapeSource t s) (.Ok z) +
          epsLap D := by
  intro r
  have hr1 : r < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by
      have : (0 : ℝ) < s := by exact_mod_cast hs
      have : 0 < 1 / (s : ℝ) := by positivity
      linarith)
  exact (discrete_laplace_approx hs hsz hD1 hD).close (tsum_lap (Real.exp_nonneg _) hr1) (.Ok z)

end OpenDP.Samplers

namespace OpenDP.Samplers

/-- `1 / (1 - e^{-1}) ≤ 2`, as `e ≥ 2`. -/
theorem inv_one_sub_exp_neg_one_le : (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹ ≤ 2 := by
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have : ENNReal.ofReal (Real.exp (-1)) ≤ 2⁻¹ := by
    rw [show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [ENNReal.inv_le_iff_inv_le, ENNReal.le_sub_iff_add_le_left (by simp)
    (this.trans (by norm_num))]
  calc ENNReal.ofReal (Real.exp (-1)) + 2⁻¹ ≤ 2⁻¹ + 2⁻¹ := by gcongr
    _ = 1 := ENNReal.inv_two_add_inv_two

/-- `1 / (1 - (1 - e^{-1})) = e ≤ 3`. -/
theorem inv_one_sub_one_sub_exp_neg_one_le :
    (1 - ENNReal.ofReal (1 - Real.exp (-1)))⁻¹ ≤ 3 := by
  have h1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have : 1 - ENNReal.ofReal (1 - Real.exp (-1)) = ENNReal.ofReal (Real.exp (-1)) := by
    rw [ENNReal.ofReal_sub _ (Real.exp_nonneg _), ENNReal.ofReal_one,
      ENNReal.sub_sub_cancel ENNReal.one_ne_top (by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1)]
  rw [this, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg, neg_neg]
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp]
  exact ENNReal.ofReal_le_ofReal (by linarith [Real.exp_one_lt_d9])

/-- **The error of `sample_discrete_laplace` is at most `72 / M!`**, `M = 2^(bitBound - 1 - D) - 1`,
where `D ≥ 1` bounds the bit length of the scale's numerator. -/
theorem epsLap_le {D : ℕ} (hD1 : 1 ≤ D) : epsLap D ≤ 72 * eps1 D := by
  have h11 : eps1 1 ≤ eps1 D := eps1_mono hD1
  have hE : ∀ D', 1 ≤ D' → epsExp D' ≤ 4 * eps1 D' := by
    intro D' hD'
    unfold epsExp
    calc (eps1 1 + eps1 D') * (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹
        ≤ (eps1 D' + eps1 D') * 2 := by
          gcongr
          · exact eps1_mono hD'
          · exact inv_one_sub_exp_neg_one_le
      _ = 4 * eps1 D' := by ring
  have hS : epsSlow ((1 : ℚ) : ℝ) 1 ≤ 8 * eps1 D := by
    unfold epsSlow
    rw [Rat.cast_one]
    calc epsExp 1 * (1 - ENNReal.ofReal (Real.exp (-1)))⁻¹ ≤ (4 * eps1 1) * 2 := by
          gcongr
          · exact hE 1 le_rfl
          · exact inv_one_sub_exp_neg_one_le
      _ ≤ (4 * eps1 D) * 2 := by gcongr
      _ = 8 * eps1 D := by ring
  unfold epsLap epsFast
  have hhalf : (1 - ENNReal.ofReal (1 / 2))⁻¹ = 2 := by
    rw [show ENNReal.ofReal (1 / 2) = 2⁻¹ by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp, ENNReal.one_sub_inv_two,
      inv_inv]
  rw [zero_add, hhalf]
  calc (epsExp D + epsSlow ((1 : ℚ) : ℝ) 1) * (1 - ENNReal.ofReal (1 - Real.exp (-1)))⁻¹ * 2
      ≤ (4 * eps1 D + 8 * eps1 D) * 3 * 2 := by
        gcongr
        · exact hE D hD1
        · exact inv_one_sub_one_sub_exp_neg_one_le
    _ = 72 * eps1 D := by ring

end OpenDP.Samplers
