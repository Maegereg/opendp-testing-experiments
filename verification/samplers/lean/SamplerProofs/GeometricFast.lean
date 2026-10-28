/-
`sample_geometric_exp_fast` (`rust/src/traits/samplers/cks20/mod.rs`), on its extracted code: for
`x = n / d > 0`, it returns `y` with probability `(1 - e^{-x}) e^{-x y}`, within `epsFast D`.

The code draws `u < d` uniformly, then loops: with probability `e^{-u/d}`
(`sample_bernoulli_exp`) it returns `⌊(v d + u) / n⌋` with `v` from
`sample_geometric_exp_slow(1)`; otherwise it draws a fresh `u` and repeats. The loop's target
from `u` is `FastMath.tgt`, whose average over `u` is the geometric distribution
(`FastMath.average`). Each iteration continues with probability at most `1 - e^{-1}`.
-/
import SamplerProofs.FastMath

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

open Classical

theorem tsum_uniform {d : ℕ} (hd : 0 < d) : ∑' r, Uniform.uniform d r = 1 := by
  rw [tsum_res]
  simp only [Uniform.uniform, tsum_zero, add_zero]
  rw [tsum_eq_sum (s := Finset.range d) fun u hu => by simp [Finset.mem_range.not.mp hu]]
  rw [Finset.sum_congr rfl (g := fun _ => (d : ℝ≥0∞)⁻¹) fun u hu => by
      simp [Finset.mem_range.mp hu],
    Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ENNReal.mul_inv_cancel (by exact_mod_cast hd.ne') (by simp)]

theorem uniform_approx {d : ℕ} (hd : 0 < d) (hs : Nat.size d < bitBound) :
    Approx (fun t => traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t d)
      (Uniform.uniform d) 0 :=
  Approx.of_hasDist (Uniform.sample_uniform_ubig_below_with_uniform d hd hs)
    (le_of_eq (tsum_uniform hd).symm)

/-- The error of `sample_geometric_exp_fast(x)` when `x`'s denominator has at most `D` bits. -/
noncomputable def epsFast (D : ℕ) : ℝ≥0∞ :=
  (epsExp D + epsSlow ((1 : ℚ) : ℝ) 1) * (1 - ENNReal.ofReal (1 - Real.exp (-1)))⁻¹

namespace Fast

variable (numer : ℤ) (d : ℕ)

/-- The extracted loop body. -/
def body : Body (Tape × ℕ) ResU := fun p =>
  traits.samplers.cks20.sample_geometric_exp_fast_with_loop.body tapeSource numer d p.1 p.2

/-- The argument of the iteration's `sample_bernoulli_exp` call: `u / d`. -/
def arg (u : ℕ) : ℚ := ((u : ℤ) : ℚ) / (d : ℚ)

/-- Accepting `u`, what the iteration returns given `v`. -/
def outV (u : ℕ) : ResU → ControlFlow ℕ ResU
  | .Ok v => .done (.Ok ((v * d + u) / numer.natAbs))
  | .Err e => .done (.Err e)

/-- Rejecting `u`, what the iteration does with the new uniform sample. -/
def outU : ResU → ControlFlow ℕ ResU
  | .Ok u' => .cont u'
  | .Err e => .done (.Err e)

/-- The iteration after `sample_bernoulli_exp`. -/
def cont (u : ℕ) : ResB → Prog (ControlFlow ℕ ResU)
  | .Ok true => bindP (fun t => traits.samplers.cks20.sample_geometric_exp_slow tapeSource t 1)
      (fun r t => ok (outV numer d u r, t))
  | .Ok false => bindP (fun t => traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t d)
      (fun r t => ok (outU r, t))
  | .Err e => fun t => ok (.done (.Err e), t)

theorem step_eq (hd : d ≠ 0) (hn : numer.natAbs ≠ 0) (u : ℕ) (t : Tape) :
    stepP (Equiv.refl _) (body numer d) u t =
      bindP (fun t => traits.samplers.cks20.sample_bernoulli_exp_with tapeSource t (arg d u))
        (cont numer d u) t := by
  simp only [stepP, body, traits.samplers.cks20.sample_geometric_exp_fast_with_loop.body, bindP,
    dashu_int.convert.UBig.as_ibig, dashu_int.ibig.IBig.Insts.CoreCloneClone.clone,
    dashu_int.ubig.UBig.Insts.CoreCloneClone.clone, dashu_ratio.rbig.RBig.from_parts, hd,
    ↓reduceIte, bind_ok, Equiv.refl_symm, Equiv.refl_apply,
    Std.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨r, t'⟩
  rcases r with b | e
  · cases b
    · simp [core.result.Result.Insts.CoreOpsTry.branch, cont, bindP]
      congr 1
      funext q
      rcases q with ⟨r2, t2⟩
      rcases r2 with u' | e
      · simp [outU]
      · simp [outU, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    · simp [core.result.Result.Insts.CoreOpsTry.branch, cont, bindP, dashu_ratio.rbig.RBig.ONE]
      congr 1
      funext q
      rcases q with ⟨r2, t2⟩
      rcases r2 with v | e
      · simp [outV, dashu_int.ubig.UBig.Insts.CoreOpsArithMulUBigUBig.mul,
          dashu_int.ubig.UBig.Insts.CoreOpsArithAddUBigUBig.add, dashu_int.ibig.IBig.into_parts,
          dashu_int.ubig.UBig.Insts.CoreOpsArithDivUBigUBig.div, hn]
      · simp [outV, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp [core.result.Result.Insts.CoreOpsTry.branch, cont,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The targets of the continuations. -/
noncomputable def nu (u : ℕ) : ResB → ControlFlow ℕ ResU → ℝ≥0∞
  | .Ok true => fun c => ∑' r, geom (Real.exp (-((1 : ℚ) : ℝ))) 0 r *
      (if c = outV numer d u r then 1 else 0)
  | .Ok false => fun c => ∑' r, Uniform.uniform d r * (if c = outU r then 1 else 0)
  | .Err e => fun c => if c = .done (.Err e) then 1 else 0

/-- The distribution of an iteration if the samplers it calls were exact. -/
noncomputable def K' (u : ℕ) (c : ControlFlow ℕ ResU) : ℝ≥0∞ :=
  ∑' r, bern (Real.exp (-(arg d u : ℝ))) r * nu numer d u r c

variable {numer d}

theorem arg_cast (u : ℕ) : ((arg d u : ℚ) : ℝ) = (u : ℝ) / d := by simp [arg]

theorem arg_den_le (hd : 0 < d) (u : ℕ) : (arg d u).den ≤ d := by
  have h := Rat.den_dvd (u : ℤ) (d : ℤ)
  rw [← Rat.intCast_div_eq_divInt] at h
  have : (arg d u).den ∣ d := by
    simpa [arg] using (Int.natCast_dvd_natCast.mp (by simpa using h))
  exact Nat.le_of_dvd hd this

theorem cont_approx (hd : 0 < d) (hs : Nat.size d < bitBound) (u : ℕ) (r : ResB) :
    Approx (cont numer d u r) (nu numer d u r) (epsSlow ((1 : ℚ) : ℝ) 1) := by
  rcases r with b | e
  · cases b
    · have h := approx_bind (uniform_approx hd hs) (fun r _ => approx_pure (outU r))
        (le_of_eq (tsum_uniform hd))
      exact h.mono (fun _ => le_rfl) (by simp)
    · have h := approx_bind (Slow.slow_approx (x := 1) (by norm_num) le_rfl (by simp))
        (fun r _ => approx_pure (outV numer d u r))
        (le_of_eq (tsum_geom (Real.exp_nonneg _) (by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by simp))))
      exact h.mono (fun _ => le_rfl) (by simp)
  · exact (approx_pure _).mono (fun _ => le_rfl) (by simp)

theorem hstep (hd : 0 < d) (hn : numer.natAbs ≠ 0) (hs : Nat.size d < bitBound) {D : ℕ}
    (hD1 : 1 ≤ D) (hD : Nat.size d ≤ D) (u : ℕ) :
    Approx (stepP (Equiv.refl _) (body numer d) u) (K' numer d u)
      (epsExp D + epsSlow ((1 : ℚ) : ℝ) 1) := by
  have ha0 : 0 ≤ arg d u := by unfold arg; positivity
  have hDa : Nat.size (arg d u).den ≤ D := (Nat.size_le_size (arg_den_le hd u)).trans hD
  have h := approx_bind (Exp.exp_approx ha0 hD1 hDa) (fun r _ => cont_approx (numer := numer) hd hs u r)
    (le_of_eq (tsum_bern (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ arg d u := by exact_mod_cast ha0
      linarith))))
  rw [show stepP (Equiv.refl _) (body numer d) u = _ from funext (step_eq numer d hd.ne' hn u)]
  exact h

/-- Sums against the continuations' targets. -/
theorem tsum_nu (u : ℕ) (r : ResB) (M : ControlFlow ℕ ResU → ℝ≥0∞) :
    ∑' c, nu numer d u r c * M c =
      match r with
      | .Ok true => ∑' v, geom (Real.exp (-((1 : ℚ) : ℝ))) 0 v * M (outV numer d u v)
      | .Ok false => ∑' w, Uniform.uniform d w * M (outU w)
      | .Err e => M (.done (.Err e)) := by
  rcases r with b | e
  · cases b
    · exact tsum_pushforward _ _ M
    · exact tsum_pushforward _ _ M
  · simp only [nu]
    rw [tsum_eq_single (.done (.Err e))]
    · simp
    · intro c hc; simp [hc]

theorem K'_cont {u u' : ℕ} (h : K' numer d u (.cont u') ≠ 0) : u' < d := by
  by_contra hne
  apply h
  refine ENNReal.tsum_eq_zero.mpr fun r => ?_
  rcases r with b | e
  · cases b
    · simp only [nu, mul_eq_zero]
      right
      refine ENNReal.tsum_eq_zero.mpr fun w => ?_
      rcases w with w | e
      · by_cases hw : u' = w
        · subst hw; simp [Uniform.uniform, hne]
        · simp [outU, hw]
      · simp [outU]
    · simp only [nu, mul_eq_zero]
      right
      refine ENNReal.tsum_eq_zero.mpr fun v => ?_
      rcases v with v | e <;> simp [outV]
  · simp [nu]

theorem cont_mass (hd : 0 < d) {u : ℕ} (hu : u < d) :
    ∑' u', K' numer d u (.cont u') ≤ ENNReal.ofReal (1 - Real.exp (-1)) := by
  rw [tsum_cont_eq]
  unfold K'
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left, tsum_nu]
  rw [tsum_resB]
  have hunif : ∑' w, Uniform.uniform d w * isCont (outU w) = 1 := by
    rw [← tsum_uniform hd]
    refine tsum_congr fun w => ?_
    rcases w with w | e
    · simp [outU, isCont]
    · simp [outU, isCont, Uniform.uniform]
  have hV : ∀ v, isCont (outV numer d u v) = 0 := fun v => by cases v <;> rfl
  simp only [hunif, hV, mul_zero, tsum_zero, zero_add, mul_one]
  simp only [isCont, bern, mul_zero, tsum_zero, add_zero]
  · refine ENNReal.ofReal_le_ofReal ?_
    have : (arg d u : ℝ) ≤ 1 := by
      rw [arg_cast, div_le_one (by exact_mod_cast hd)]; exact_mod_cast hu.le
    linarith [Real.exp_le_exp.mpr (show -(1 : ℝ) ≤ -(arg d u : ℝ) by linarith)]

theorem super (hn : 0 < numer.natAbs) (hd : 0 < d) (u : ℕ) (b : ResU) :
    ∑' c, K' numer d u c * contOr (FastMath.tgt numer.natAbs d) c b ≤
      FastMath.tgt numer.natAbs d u b := by
  unfold K'
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left, tsum_nu]
  rw [tsum_resB]
  -- The uniform branch averages the targets.
  have havg : ∑' w, Uniform.uniform d w * contOr (FastMath.tgt numer.natAbs d) (outU w) b =
      ∑ w ∈ Finset.range d, (d : ℝ≥0∞)⁻¹ * FastMath.tgt numer.natAbs d w b := by
    rw [tsum_res]
    simp only [outU, contOr, Uniform.uniform, zero_mul, tsum_zero, add_zero]
    rw [tsum_eq_sum (s := Finset.range d) fun w hw => by simp [Finset.mem_range.not.mp hw]]
    exact Finset.sum_congr rfl fun w hw => by simp [Finset.mem_range.mp hw]
  simp only [havg, bern, tsum_zero, add_zero, zero_mul]
  have hp : Real.exp (-(arg d u : ℝ)) = FastMath.pacc d u := by rw [arg_cast]; rfl
  rcases b with y | e
  · rw [FastMath.average hn hd, hp]
    simp only [FastMath.tgt]
    refine le_of_eq ?_
    congr 2
    rw [tsum_res, FastMath.G]
    simp only [geom, outV, contOr, zero_le, ↓reduceIte, Nat.sub_zero, zero_mul, tsum_zero,
      add_zero, Rat.cast_one, core.result.Result.Ok.injEq, FastMath.gw]
  · simp [FastMath.tgt, contOr, outV, geom, tsum_res]

theorem q_lt_one : ENNReal.ofReal (1 - Real.exp (-1)) < 1 := by
  rw [← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith [Real.exp_pos (-1)])

/-- The loop, from `u < d`. -/
theorem loop_approx (hn : 0 < numer.natAbs) (hd : 0 < d) (hs : Nat.size d < bitBound) {D : ℕ}
    (hD1 : 1 ≤ D) (hD : Nat.size d ≤ D) {u : ℕ} (hu : u < d) :
    Approx (loopP (Equiv.refl _) (body numer d) u) (FastMath.tgt numer.natAbs d u) (epsFast D) :=
  approx_loop (I := fun u => u < d) (fun u _ => hstep hd hn.ne' hs hD1 hD u)
    (fun _ _ _ h => K'_cont h) (fun _ hu => cont_mass hd hu) q_lt_one
    (fun u _ b => super hn hd u b) hu

variable (numer d)

/-- After the first uniform sample: the loop, or the error. -/
def entry : ResU → Prog ResU
  | .Ok u => loopP (Equiv.refl _) (body numer d) u
  | .Err e => fun t => ok (.Err e, t)

/-- The targets of `entry`. -/
noncomputable def entryT : ResU → ResU → ℝ≥0∞
  | .Ok u => FastMath.tgt numer.natAbs d u
  | .Err e => fun b => if b = .Err e then 1 else 0

theorem code_eq {x : ℚ} (hx : x ≠ 0) (t : Tape) :
    traits.samplers.cks20.sample_geometric_exp_fast_with tapeSource t x =
      bindP (fun t => traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t x.den)
        (entry x.num x.den) t := by
  simp [traits.samplers.cks20.sample_geometric_exp_fast_with, dashu_ratio.rbig.RBig.is_zero, hx,
    dashu_ratio.rbig.RBig.into_parts, dashu_int.ubig.UBig.Insts.CoreCloneClone.clone, bindP]
  congr 1
  funext p
  rcases p with ⟨r, t'⟩
  rcases r with u | e
  · simp [core.result.Result.Insts.CoreOpsTry.branch, entry, loopP]
    rfl
  · simp [core.result.Result.Insts.CoreOpsTry.branch, entry,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

variable {numer d}

/-- **`sample_geometric_exp_fast(x)` is geometric with ratio `e^{-x}`**, for `x > 0` whose
denominator's bit length fits in a `usize`, within `epsFast D` (`D ≥ 1` bounds that bit length). -/
theorem fast_approx {x : ℚ} (hx : 0 < x) (hs : Nat.size x.den < bitBound) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : Nat.size x.den ≤ D) :
    Approx (fun t => traits.samplers.cks20.sample_geometric_exp_fast_with tapeSource t x)
      (geom (Real.exp (-(x : ℝ))) 0) (epsFast D) := by
  have hd := x.den_pos
  have hn : 0 < x.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hx.ne')
  rw [show (fun t => traits.samplers.cks20.sample_geometric_exp_fast_with tapeSource t x) = _ from
    funext (code_eq hx.ne')]
  have h := approx_bind (uniform_approx hd hs) (k := entry x.num x.den)
    (ν := entryT x.num x.den) (ε₂ := epsFast D)
    (fun r hr => by
      rcases r with u | e
      · have hu : u < x.den := by
          by_contra h; exact hr (by simp [Uniform.uniform, h])
        exact loop_approx hn hd hs hD1 hD hu
      · exact (approx_pure (.Err e : ResU)).mono (fun _ => le_rfl) (by simp))
    (le_of_eq (tsum_uniform hd))
  refine h.mono (fun b => ?_) (by simp)
  rw [tsum_res]
  simp only [entryT, Uniform.uniform, zero_mul, tsum_zero, add_zero]
  rw [tsum_eq_sum (s := Finset.range x.den) fun u hu => by simp [Finset.mem_range.not.mp hu],
    Finset.sum_congr rfl (g := fun u => (x.den : ℝ≥0∞)⁻¹ * FastMath.tgt x.num.natAbs x.den u b)
      fun u hu => by simp [Finset.mem_range.mp hu]]
  rcases b with y | e
  · rw [FastMath.average hn hd]
    -- `x = n / d`.
    have hxr : ((x : ℚ) : ℝ) = (x.num.natAbs : ℝ) / x.den := by
      rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (Rat.num_pos.mpr hx).le)]
    simp only [geom, zero_le, ↓reduceIte, Nat.sub_zero, FastMath.A, hxr]
    exact le_rfl
  · simp [FastMath.tgt]

end Fast

end OpenDP.Samplers
