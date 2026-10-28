/-
`sample_standard_bernoulli` and `sample_bernoulli_rational` (`rust/src/traits/samplers/bernoulli`),
on their extracted code: a fair coin, and a coin with probability `q ∈ [0, 1]` of `true`.
-/
import SamplerProofs.Uniform

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

open Classical

/-- The results of the samplers that return a `bool`. -/
abbrev ResB := core.result.Result Bool error.Error

/-- The Bernoulli distribution with probability `p` of `true` (no errors). -/
noncomputable def bern (p : ℝ) : ResB → ℝ≥0∞
  | .Ok true => ENNReal.ofReal p
  | .Ok false => ENNReal.ofReal (1 - p)
  | .Err _ => 0

/-- A sum over the results of a sampler. -/
theorem tsum_res {X : Type} (g : core.result.Result X error.Error → ℝ≥0∞) :
    ∑' r, g r = ∑' x, g (.Ok x) + ∑' e, g (.Err e) := by
  let eq : (X ⊕ error.Error) ≃ core.result.Result X error.Error :=
    { toFun := Sum.elim .Ok .Err
      invFun := fun r => match r with | .Ok b => .inl b | .Err e => .inr e
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun r => by cases r <;> rfl }
  rw [← eq.tsum_eq, ENNReal.summable.tsum_sum ENNReal.summable]
  rfl

/-- A sum over the results of a `bool` sampler. -/
theorem tsum_resB (g : ResB → ℝ≥0∞) :
    ∑' r, g r = g (.Ok true) + g (.Ok false) + ∑' e, g (.Err e) := by
  let eq : (Bool ⊕ error.Error) ≃ ResB :=
    { toFun := Sum.elim .Ok .Err
      invFun := fun r => match r with | .Ok b => .inl b | .Err e => .inr e
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun r => by cases r <;> rfl }
  rw [← eq.tsum_eq, ENNReal.summable.tsum_sum ENNReal.summable, tsum_fintype]
  simp [eq, add_comm]

theorem tsum_bern {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∑' r, bern p r = 1 := by
  rw [tsum_resB]
  simp only [bern, tsum_zero, add_zero]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

/-! ### `sample_standard_bernoulli` -/

theorem u8_and_one (d : Std.U8) : (d &&& 1#u8 = 1#u8) ↔ d.val % 2 = 1 := by
  rw [UScalar.eq_equiv, UScalar.val_and, show (1#u8 : Std.U8).val = 1 by simp,
    Nat.and_one_is_mod]

/-- The extracted `sample_standard_bernoulli_with` reads one byte and returns its low bit. -/
theorem standard_bernoulli_eq (t : Tape) :
    traits.samplers.bernoulli.sample_standard_bernoulli_with tapeSource t =
      bindP (draw 1) (fun w t' => ok (.Ok (decide (w.headD 0#u8 &&& 1#u8 = 1#u8)), t')) t := by
  simp [traits.samplers.bernoulli.sample_standard_bernoulli_with, tapeSource, Array.to_slice_mut,
    Array.to_slice, Array.from_slice, Array.index_usize, lift,
    core.result.Result.Insts.CoreOpsTry.branch, Tape.take, bindP, draw]
  exact decide_eq_decide.mpr Iff.rfl

/-- **`sample_standard_bernoulli` is a fair coin.** -/
theorem standard_bernoulli_dist :
    HasDist (fun t => traits.samplers.bernoulli.sample_standard_bernoulli_with tapeSource t)
      (bern (1 / 2)) := by
  have h := hasDist_bind (hasDist_draw 1)
    (fun w => hasDist_pure (.Ok (decide (w.headD 0#u8 &&& 1#u8 = 1#u8)) : ResB))
  rw [show (fun t => traits.samplers.bernoulli.sample_standard_bernoulli_with tapeSource t) =
    bindP (draw 1) (fun w t' => ok (.Ok (decide (w.headD 0#u8 &&& 1#u8 = 1#u8)), t')) from
    funext standard_bernoulli_eq]
  refine ⟨h.1, fun r => ?_⟩
  rw [h.2 r]
  dsimp only
  -- Words of length 1 are the bytes; half of them are odd.
  have hw : ∀ w : List Std.U8, (if w.length = 1 then (256 : ℝ≥0∞)⁻¹ ^ 1 else 0) *
      (if r = .Ok (decide (w.headD 0#u8 &&& 1#u8 = 1#u8)) then 1 else 0) =
      if w.length = 1 then (256 : ℝ≥0∞)⁻¹ *
        (if r = .Ok (decide (beValue w % 2 = 1)) then 1 else 0) else 0 := by
    intro w
    by_cases hl : w.length = 1
    · obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hl
      simp [beValue, u8_and_one]
    · simp [hl]
  rw [tsum_congr hw, tsum_words (fun v => (256 : ℝ≥0∞)⁻¹ *
    (if r = .Ok (decide (v % 2 = 1)) then 1 else 0)) 1, ← Finset.mul_sum]
  rcases r with b | e
  · have hcount : ∀ b : Bool, (∑ v ∈ Finset.range (256 ^ 1),
        if (core.result.Result.Ok b : ResB) = .Ok (decide (v % 2 = 1)) then (1 : ℝ≥0∞) else 0) =
        128 := by
      intro b
      simp only [core.result.Result.Ok.injEq, pow_one]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
      cases b <;> rfl
    rw [hcount]
    cases b
    · simp only [bern]
      rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
      rw [show (256 : ℝ≥0∞) = 2 * 128 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]
    · simp only [bern]
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
        ENNReal.ofReal_ofNat]
      rw [show (256 : ℝ≥0∞) = 2 * 128 by norm_num, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]
  · simp [bern]

/-! ### `sample_bernoulli_rational` -/

theorem rat_num_le_den {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) : q.num.natAbs ≤ q.den := by
  have hnum : (0 : ℤ) ≤ q.num := Rat.num_nonneg.mpr h0
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have : (q.num : ℚ) ≤ q.den := by
    rw [← div_le_one hden, Rat.num_div_den]; exact h1
  have : q.num ≤ (q.den : ℤ) := by exact_mod_cast this
  omega

/-- What `sample_bernoulli_rational` returns, given the uniform sample: `true` if it is below the
numerator `n`. -/
def ratOut (n : ℕ) : Uniform.Res → ResB
  | .Ok s => .Ok (decide ((s : ℕ) < n))
  | .Err e => .Err e

/-- The extracted `sample_bernoulli_rational_with` on `q ∈ [0, 1]`: a uniform sample below the
denominator, compared with the numerator. -/
theorem bernoulli_rational_eq {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (t : Tape) :
    traits.samplers.bernoulli.sample_bernoulli_rational_with tapeSource t q =
      bindP (fun t => traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t q.den)
        (fun r t' => ok (ratOut q.num.natAbs r, t')) t := by
  have hle := rat_num_le_den h0 h1
  have hgt : compare q.num.natAbs q.den ≠ Ordering.gt := by
    rw [Ne, Nat.compare_eq_gt]; omega
  simp [traits.samplers.bernoulli.sample_bernoulli_rational_with,
    dashu_ratio.rbig.RBig.into_parts, dashu_int.ibig.IBig.into_parts,
    core.cmp.PartialOrd.gt.trait_default, core.cmp.PartialOrd.gt.default,
    core.cmp.PartialOrd.gt_body, dashu_int.ubig.UBig.Insts.CoreCmpPartialOrdUBig.partial_cmp,
    not_lt.mpr h0, hgt, bindP]
  congr 1
  funext p
  rcases p with ⟨r, t'⟩
  rcases r with s | e
  · simp [core.result.Result.map, ratOut,
      traits.samplers.bernoulli.sample_bernoulli_rational_with.closure.Insts.CoreOpsFunctionFnOnceTupleUBigBool.call_once,
      core.cmp.PartialOrd.gt.trait_default, core.cmp.PartialOrd.gt.default,
      core.cmp.PartialOrd.gt_body, dashu_int.ubig.UBig.Insts.CoreCmpPartialOrdUBig.partial_cmp,
      Nat.compare_eq_gt]
  · simp [core.result.Result.map, ratOut]

/-- **`sample_bernoulli_rational(q)` returns `true` with probability `q`**, for `q ∈ [0, 1]`
whose denominator's bit length fits in a `usize`. -/
theorem bernoulli_rational_dist {q : ℚ} (h0 : 0 ≤ q) (h1 : q ≤ 1)
    (hs : Nat.size q.den < 2 ^ UScalarTy.Usize.numBits) :
    HasDist (fun t => traits.samplers.bernoulli.sample_bernoulli_rational_with tapeSource t q)
      (bern q) := by
  have hu := Uniform.sample_uniform_ubig_below_with_uniform q.den q.den_pos hs
  have h := hasDist_bind hu (fun r => hasDist_pure (ratOut q.num.natAbs r))
  rw [show (fun t => traits.samplers.bernoulli.sample_bernoulli_rational_with tapeSource t q) = _
    from funext (bernoulli_rational_eq h0 h1)]
  refine ⟨h.1, fun r => ?_⟩
  rw [h.2 r]
  dsimp only
  -- Only the uniform samples below the denominator have mass.
  have hle := rat_num_le_den h0 h1
  have hd : (0 : ℝ≥0∞) < q.den := by exact_mod_cast q.den_pos
  have hq : (q : ℝ) = (q.num.natAbs : ℝ) / q.den := by
    rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast Rat.num_nonneg.mpr h0)]
  have hsum : (∑' a : Uniform.Res, Uniform.uniform q.den a *
      (if r = ratOut q.num.natAbs a then 1 else 0)) =
      ∑ s ∈ Finset.range q.den, (q.den : ℝ≥0∞)⁻¹ *
        (if r = .Ok (decide (s < q.num.natAbs)) then 1 else 0) := by
    rw [tsum_res]
    simp only [Uniform.uniform, ratOut, zero_mul, tsum_zero, add_zero]
    rw [tsum_eq_sum (s := Finset.range q.den) fun s hs => by
      simp [Finset.mem_range.not.mp hs]]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [Finset.mem_range.mp hs, ↓reduceIte]
    by_cases hr : r = .Ok (decide (s < q.num.natAbs)) <;> simp [hr]
  rw [hsum, ← Finset.mul_sum]
  rcases r with b | e
  · simp only [core.result.Result.Ok.injEq]
    have hcount : (∑ s ∈ Finset.range q.den,
        if b = decide (s < q.num.natAbs) then (1 : ℝ≥0∞) else 0) =
        if b then (q.num.natAbs : ℝ≥0∞) else ((q.den - q.num.natAbs : ℕ) : ℝ≥0∞) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
        mul_one]
      cases b
      · simp only [Bool.false_eq, decide_eq_false_iff_not, not_lt]
        rw [show (Finset.range q.den).filter (fun s => q.num.natAbs ≤ s) =
          Finset.Ico q.num.natAbs q.den by ext; simp [and_comm]]
        simp
      · simp only [Bool.true_eq, decide_eq_true_eq, ↓reduceIte]
        rw [show (Finset.range q.den).filter (fun s => s < q.num.natAbs) =
          Finset.range q.num.natAbs by ext; simp; omega]
        simp
    rw [hcount]
    have hden0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_pos.ne'
    cases b
    · simp only [bern, Bool.false_eq_true, ↓reduceIte]
      rw [hq, show (1 : ℝ) - q.num.natAbs / q.den = ((q.den - q.num.natAbs : ℕ) : ℝ) / q.den by
        rw [Nat.cast_sub hle]; field_simp]
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast q.den_pos), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
    · simp only [bern, ↓reduceIte]
      rw [hq, ENNReal.ofReal_div_of_pos (by exact_mod_cast q.den_pos), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul]
  · simp [bern]

end OpenDP.Samplers
