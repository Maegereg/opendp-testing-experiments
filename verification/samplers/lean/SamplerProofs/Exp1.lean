/-
`sample_bernoulli_exp1` (`rust/src/traits/samplers/cks20/mod.rs`), on its extracted code: for
`x ∈ [0, 1]`, it returns `true` with probability `e^{-x}`, up to an error `eps1 D`.

The loop draws `Bernoulli(x / k)` for `k = 1, 2, ...` until it draws `false`, and returns whether
that `k` is odd. It stops at `k` with probability `x^{k-1}/(k-1)! (1 - x/k)`; summing over odd `k`
gives `e^{-x}` (`ExpSeries.lean`).

The error: the denominator of `x / k` grows with `k`, and once its bit length no longer fits in a
`usize` the uniform sampler fails (the real program could not allocate the number). With `D` at
least the bit length of `x`'s denominator, every `k ≤ M = 2^(bitBound - 1 - D) - 1` is fine, and
the loop gets past `M` with probability at most `x^M / M! ≤ 1 / M!` (`eps1 D`).
-/
import SamplerProofs.Bernoulli
import SamplerProofs.Approx
import SamplerProofs.ExpSeries

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers

/-- Bit lengths must be below this: `bit_len` returns a `usize`. -/
abbrev bitBound : ℕ := 2 ^ UScalarTy.Usize.numBits

/-- The error of `sample_bernoulli_exp1` when the denominator of `x` has at most `D` bits:
`1 / M!` with `M = 2^(bitBound - 1 - D) - 1`. -/
noncomputable def eps1 (D : ℕ) : ℝ≥0∞ :=
  ((Nat.factorial (2 ^ (bitBound - 1 - D) - 1) : ℕ) : ℝ≥0∞)⁻¹

theorem eps1_mono {D D' : ℕ} (h : D ≤ D') : eps1 D ≤ eps1 D' := by
  unfold eps1
  refine ENNReal.inv_le_inv.mpr ?_
  exact_mod_cast Nat.factorial_le
    (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 1)

open Classical in
/-- Sums against a distribution pushed forward through `g`. -/
theorem tsum_pushforward {R C : Type} (μ : R → ℝ≥0∞) (g : R → C) (F : C → ℝ≥0∞) :
    ∑' c, (∑' r, μ r * (if c = g r then 1 else 0)) * F c = ∑' r, μ r * F (g r) := by
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun r => ?_
  rw [tsum_eq_single (g r)]
  · simp
  · intro c hc; simp [hc]

/-- The uniform sampler fails when the bit length of `upper` does not fit in a `usize`. -/
theorem uniform_fail {upper : ℕ} (hs : ¬ Nat.size upper < bitBound) (t : Tape) :
    traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t upper =
      fail .integerOverflow := by
  have hs' : ¬ Nat.size upper < 2 ^ System.Platform.numBits := by
    simpa [bitBound, UScalarTy.numBits] using hs
  simp [traits.samplers.uniform.sample_uniform_ubig_below_with,
    dashu_int.ubig.UBig.Insts.Dashu_baseBitBitTest.bit_len, usizeOfNat, hs']

theorem bindP_fail {α β : Type} (k : α → Prog β) (e : Error) (t : Tape) :
    bindP (fun _ => fail e) k t = fail e := by
  simp [bindP]

namespace Exp1

open Classical

variable (x : ℚ)

/-- The extracted loop body (the counter is incremented by one). -/
def body : Body (Tape × ℕ) ResB := fun p =>
  traits.samplers.cks20.sample_bernoulli_exp1_loop.body tapeSource (1 : ℕ) x p.1 p.2

/-- What the iteration at `k` does with the Bernoulli sample. -/
def out (k : ℕ) : ResB → ControlFlow ℕ ResB
  | .Ok true => .cont (k + 1)
  | .Ok false => .done (.Ok (decide (k % 2 = 1)))
  | .Err e => .done (.Err e)

theorem step_eq {k : ℕ} (hk : 1 ≤ k) (t : Tape) :
    stepP (Equiv.refl _) (body x) k t =
      bindP (fun t => traits.samplers.bernoulli.sample_bernoulli_rational_with tapeSource t (x / k))
        (fun r t' => ok (out k r, t')) t := by
  simp only [stepP, body, traits.samplers.cks20.sample_bernoulli_exp1_loop.body, bindP,
    dashu_ratio.rbig.RBig.Insts.CoreCloneClone.clone,
    dashu_ratio.rbig.RBig.Insts.CoreOpsArithDivSharedRUBigRBig.div,
    show k ≠ 0 by omega, ↓reduceIte, bind_ok, Equiv.refl_symm, Equiv.refl_apply, Std.bind_assoc]
  congr 1
  funext p
  rcases p with ⟨r, t'⟩
  rcases r with b | e
  · cases b <;> simp [core.result.Result.Insts.CoreOpsTry.branch, out,
      dashu_int.ubig.UBig.Insts.CoreOpsArithAddAssignUBig.add_assign,
      dashu_int.ubig.UBig.Insts.CoreOpsArithRemU8U8.rem, UScalar.eq_equiv, U8.ofNatCore_val_eq]
  · simp [core.result.Result.Insts.CoreOpsTry.branch, out,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The code is the loop from `k = 1`. -/
theorem code_eq : (fun t => traits.samplers.cks20.sample_bernoulli_exp1 tapeSource t x) =
    loopP (Equiv.refl _) (body x) 1 := by
  funext t
  simp only [traits.samplers.cks20.sample_bernoulli_exp1,
    traits.samplers.cks20.sample_bernoulli_exp1_loop, dashu_int.ubig.UBig.ONE, bind_ok, loopP,
    Equiv.refl_symm, Equiv.refl_apply]
  rfl

/-- The probability that the Bernoulli sample at `k` is `true`. -/
noncomputable def p (k : ℕ) : ℝ := ((x / k : ℚ) : ℝ)

theorem p_eq (k : ℕ) : p x k = (x : ℝ) / k := by simp [p]

/-- The iterations whose uniform sample fits. -/
def Good (k : ℕ) : Prop := Nat.size (x / k).den < bitBound

/-- The distribution of an iteration if nothing failed. -/
noncomputable def K' (k : ℕ) (c : ControlFlow ℕ ResB) : ℝ≥0∞ :=
  ∑' r, bern (p x k) r * (if c = out k r then 1 else 0)

/-- The distribution of an iteration. -/
noncomputable def K (k : ℕ) (c : ControlFlow ℕ ResB) : ℝ≥0∞ := if Good x k then K' x k c else 0

variable {x}

theorem p_mem (h0 : 0 ≤ x) (h1 : x ≤ 1) {k : ℕ} (hk : 1 ≤ k) : 0 ≤ x / k ∧ x / k ≤ 1 := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  exact ⟨div_nonneg h0 (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩

theorem hasDist_step (h0 : 0 ≤ x) (h1 : x ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    HasDist (stepP (Equiv.refl _) (body x) k) (K x k) := by
  obtain ⟨hp0, hp1⟩ := p_mem h0 h1 hk
  by_cases hg : Good x k
  · have h := hasDist_bind (bernoulli_rational_dist hp0 hp1 hg)
      (fun r => hasDist_pure (out k r))
    rw [show stepP (Equiv.refl _) (body x) k = _ from funext (step_eq x hk)]
    refine ⟨h.1, fun c => ?_⟩
    rw [h.2 c]
    simp only [K, hg, ↓reduceIte, K', p]
  · have hf : stepP (Equiv.refl _) (body x) k = fun _ => fail .integerOverflow := by
      funext t
      rw [step_eq x hk, bindP]
      rw [bernoulli_rational_eq hp0 hp1, bindP, uniform_fail hg, bind_fail, bind_fail]
    rw [hf]
    have := hasDist_fail (α := ControlFlow ℕ ResB) .integerOverflow
    refine ⟨this.1, fun c => ?_⟩
    rw [this.2 c]
    simp [K, hg]

theorem K_le (k : ℕ) (c : ControlFlow ℕ ResB) : K x k c ≤ K' x k c := by
  unfold K; split_ifs <;> simp

theorem K'_cont {k k' : ℕ} (h : K' x k (.cont k') ≠ 0) : k' = k + 1 := by
  by_contra hne
  apply h
  refine ENNReal.tsum_eq_zero.mpr fun r => ?_
  rcases r with b | e
  · cases b
    · simp [out]
    · simp only [out, ControlFlow.cont.injEq]
      simp [hne]
  · simp [out]

/-! ### The target -/

variable (x)

/-- The probability of reaching `k + i` from `k`: `∏_{j<i} x / (k + j)`. -/
noncomputable def reach : ℕ → ℕ → ℝ≥0∞
  | 0, _ => 1
  | i + 1, k => ENNReal.ofReal (p x k) * reach i (k + 1)

/-- The probability that the loop, from `k`, stops at `k + i` and returns `b`. -/
noncomputable def term (k : ℕ) (b : ResB) (i : ℕ) : ℝ≥0∞ :=
  reach x i k * (ENNReal.ofReal (1 - p x (k + i)) *
    (if b = .Ok (decide ((k + i) % 2 = 1)) then 1 else 0))

/-- From `k`, the loop returns `b` with probability `target k b`. -/
noncomputable def target (k : ℕ) (b : ResB) : ℝ≥0∞ := ∑' i, term x k b i

variable {x}

theorem target_eq (k : ℕ) (b : ResB) :
    target x k b = ENNReal.ofReal (p x k) * target x (k + 1) b +
      ENNReal.ofReal (1 - p x k) * (if b = .Ok (decide (k % 2 = 1)) then 1 else 0) := by
  have hs : ∑' i, term x k b (i + 1) = ENNReal.ofReal (p x k) * target x (k + 1) b := by
    rw [target, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [term, term, reach, show k + (i + 1) = k + 1 + i by ring, mul_assoc]
  conv_lhs => rw [target, tsum_eq_zero_add' ENNReal.summable, hs]
  rw [add_comm]
  simp only [term, reach, add_zero, one_mul]

theorem super (k : ℕ) (b : ResB) :
    ∑' c, K' x k c * contOr (target x) c b ≤ target x k b := by
  unfold K'
  rw [tsum_pushforward, tsum_resB, target_eq]
  simp [bern, out, contOr, add_comm]

/-! ### `target 1 = Bernoulli(e^{-x})` -/

theorem reach_eq (h0 : 0 ≤ x) : ∀ i k, reach x i k =
    ENNReal.ofReal (∏ j ∈ Finset.range i, (x : ℝ) / (k + j))
  | 0, k => by simp [reach]
  | i + 1, k => by
    rw [reach, reach_eq h0 i (k + 1), p_eq, ← ENNReal.ofReal_mul (by positivity),
      Finset.prod_range_succ']
    congr 1
    rw [mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      push_cast; ring_nf
    · simp

theorem reach_one (h0 : 0 ≤ x) (i : ℕ) : reach x i 1 = ENNReal.ofReal (expTerm x i) := by
  rw [reach_eq h0, expTerm]
  congr 1
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  congr 1
  exact Finset.prod_congr rfl fun j _ => by ring

theorem target_one (h0 : 0 ≤ x) (h1 : x ≤ 1) (b : ResB) :
    target x 1 b = bern (Real.exp (-(x : ℝ))) b := by
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  -- Each term is `expTerm i - expTerm (i+1)` where the parity matches.
  have hterm : ∀ i, reach x i 1 * ENNReal.ofReal (1 - p x (1 + i)) =
      ENNReal.ofReal (expTerm x i - expTerm x (i + 1)) := by
    intro i
    have hpi : 1 - p x (1 + i) = 1 - (x : ℝ) / (i + 1) := by rw [p_eq]; push_cast; ring
    rw [reach_one h0, hpi, ← ENNReal.ofReal_mul (expTerm_nonneg hx0 i), expTerm_succ]
    congr 1
    ring
  have hsum : ∀ (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ),
      (∀ i, f i = if P i then expTerm x i - expTerm x (i + 1) else 0) →
      HasSum f (∑' i, f i) →
      ∑' i, reach x i 1 * (ENNReal.ofReal (1 - p x (1 + i)) * (if P i then 1 else 0)) =
        ENNReal.ofReal (∑' i, f i) := by
    intro P _ f hf _
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => by
        rw [hf i]; split_ifs <;> simp [expTerm_sub_nonneg hx0 hx1])
      (by refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (Real.summable_pow_div_factorial x)
          · rw [hf i]; split_ifs <;> simp [expTerm_sub_nonneg hx0 hx1]
          · rw [hf i]; split_ifs
            · rw [← expTerm]; linarith [expTerm_nonneg hx0 (i + 1)]
            · exact expTerm_nonneg hx0 i)]
    refine tsum_congr fun i => ?_
    rw [← mul_assoc, hterm, hf i]
    split_ifs <;> simp
  rcases b with b | e
  · cases b
    · -- `false`: the loop stops at an even `k = 1 + i`, that is `i` odd.
      have := hsum (fun i => i % 2 = 1) (oddTerm x) (fun i => rfl) (hasSum_exp_odd x).summable.hasSum
      rw [(hasSum_exp_odd x).tsum_eq] at this
      rw [show bern (Real.exp (-(x : ℝ))) (.Ok false) = ENNReal.ofReal (1 - Real.exp (-(x : ℝ)))
        from rfl, ← this, target]
      refine tsum_congr fun i => ?_
      have hi : ((core.result.Result.Ok false : ResB) = .Ok (decide ((1 + i) % 2 = 1))) ↔
          i % 2 = 1 := by
        simp only [core.result.Result.Ok.injEq, Bool.false_eq, decide_eq_false_iff_not]; omega
      simp only [term, hi]
    · have := hsum (fun i => i % 2 = 0) (evenTerm x) (fun i => rfl)
        (hasSum_exp_even x).summable.hasSum
      rw [(hasSum_exp_even x).tsum_eq] at this
      rw [show bern (Real.exp (-(x : ℝ))) (.Ok true) = ENNReal.ofReal (Real.exp (-(x : ℝ)))
        from rfl, ← this, target]
      refine tsum_congr fun i => ?_
      have hi : ((core.result.Result.Ok true : ResB) = .Ok (decide ((1 + i) % 2 = 1))) ↔
          i % 2 = 0 := by
        simp only [core.result.Result.Ok.injEq, Bool.true_eq, decide_eq_true_eq]; omega
      simp only [term, hi]
  · simp [target, term, bern]

/-! ### The probability of failing -/

theorem good_of_le {D : ℕ} (hD : Nat.size x.den ≤ D) {k : ℕ} (hk : 1 ≤ k)
    (hkM : k ≤ 2 ^ (bitBound - 1 - D) - 1) : Good x k := by
  have hb : 1 ≤ bitBound := Nat.one_le_two_pow
  by_cases hDb : D ≤ bitBound - 1
  · have hdvd : (x / k).den ∣ x.den * k := by
      have := Rat.mul_den_dvd x (k : ℚ)⁻¹
      rwa [Rat.inv_natCast_den_of_pos (by omega), ← div_eq_mul_inv] at this
    have hle : (x / k).den ≤ x.den * k := Nat.le_of_dvd (by positivity) hdvd
    have hx : x.den < 2 ^ D := Nat.size_le.mp hD
    have hk2 : k < 2 ^ (bitBound - 1 - D) := by
      have := Nat.one_le_two_pow (n := bitBound - 1 - D); omega
    have : x.den * k < 2 ^ (bitBound - 1) := by
      calc x.den * k < 2 ^ D * 2 ^ (bitBound - 1 - D) := Nat.mul_lt_mul'' hx hk2
        _ = 2 ^ (bitBound - 1) := by rw [← pow_add]; congr 1; omega
    have := Nat.size_le.mpr (lt_of_le_of_lt hle this)
    unfold Good; omega
  · have : bitBound - 1 - D = 0 := by omega
    rw [this] at hkM
    simp at hkM; omega

theorem reach_le (h0 : 0 ≤ x) (h1 : x ≤ 1) (M : ℕ) :
    reach x M 1 ≤ ((Nat.factorial M : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [reach_one h0, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [expTerm, div_eq_mul_inv]
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  calc (x : ℝ) ^ M * (Nat.factorial M : ℝ)⁻¹ ≤ 1 * (Nat.factorial M : ℝ)⁻¹ := by
        gcongr; exact pow_le_one₀ hx0 hx1
    _ = _ := one_mul _

/-- The chain bound: if the next `m` iterations from `k` are fine, the loop returns with
probability at least `1 - reach m k`. -/
theorem chain (h0 : 0 ≤ x) (h1 : x ≤ 1) : ∀ m k, 1 ≤ k → (∀ j < m, Good x (k + j)) →
    ∀ n, m ≤ n → 1 ≤ (∑' b, loopCut (K x) n k b) + reach x m k
  | 0, k, _, _, n, _ => by simp [reach]
  | m + 1, k, hk, hg, n, hn => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ih := chain h0 h1 m (k + 1) (by omega) (fun j hj => by
      have := hg (j + 1) (by omega); rwa [show k + (j + 1) = k + 1 + j by ring] at this)
      n' (by omega)
    have hgk : Good x k := by simpa using hg 0 (by omega)
    obtain ⟨hp0, hp1⟩ := p_mem h0 h1 hk
    have hpr0 : (0 : ℝ) ≤ p x k := by rw [p]; exact_mod_cast hp0
    have hpr1 : p x k ≤ 1 := by rw [p]; exact_mod_cast hp1
    rw [tsum_loopCut_succ]
    simp only [K, hgk, ↓reduceIte, K']
    rw [tsum_pushforward, tsum_resB]
    simp only [bern, out, contTot, mul_one, tsum_zero, add_zero]
    rw [reach]
    have hone : ENNReal.ofReal (p x k) + ENNReal.ofReal (1 - p x k) = 1 := by
      rw [← ENNReal.ofReal_add hpr0 (by linarith)]; simp
    calc 1 = ENNReal.ofReal (p x k) * 1 + ENNReal.ofReal (1 - p x k) := by rw [mul_one, hone]
      _ ≤ ENNReal.ofReal (p x k) * ((∑' b, loopCut (K x) n' (k + 1) b) + reach x m (k + 1)) +
          ENNReal.ofReal (1 - p x k) := by gcongr
      _ = _ := by ring

/-! ### The theorem -/

/-- **`sample_bernoulli_exp1(x)` returns `true` with probability `e^{-x}`**, for `x ∈ [0, 1]`,
within `eps1 D`, where `D` bounds the bit length of `x`'s denominator. -/
theorem exp1_approx (h0 : 0 ≤ x) (h1 : x ≤ 1) {D : ℕ} (hD : Nat.size x.den ≤ D) :
    Approx (fun t => traits.samplers.cks20.sample_bernoulli_exp1 tapeSource t x)
      (bern (Real.exp (-(x : ℝ)))) (eps1 D) := by
  rw [code_eq]
  have hI : ∀ k, 1 ≤ k → ∀ k', K x k (.cont k') ≠ 0 → 1 ≤ k' := fun k _ k' h => by
    have := K'_cont fun h0 => h (le_antisymm (h0 ▸ K_le k _) bot_le)
    omega
  have hdist := hasDist_loop_inv (I := fun k => 1 ≤ k) (fun k hk => hasDist_step h0 h1 hk) hI
    (le_refl 1)
  refine ⟨_, hdist, fun b => iSup_le fun n => ?_, ?_⟩
  · rw [← target_one h0 h1]
    exact loopCut_le_of_super (fun k _ c => K_le k c) hI (fun k _ b => super k b) n 1 le_rfl b
  · set M := 2 ^ (bitBound - 1 - D) - 1
    have h := chain h0 h1 M 1 le_rfl (fun j hj => good_of_le hD (by omega) (by omega)) M le_rfl
    rw [tsum_iSup_loopCut]
    calc 1 ≤ (∑' b, loopCut (K x) M 1 b) + reach x M 1 := h
      _ ≤ (⨆ n, ∑' b, loopCut (K x) n 1 b) + eps1 D := by
          gcongr
          · exact le_iSup (fun n => ∑' b, loopCut (K x) n 1 b) M
          · exact reach_le h0 h1 M

end Exp1

end OpenDP.Samplers
