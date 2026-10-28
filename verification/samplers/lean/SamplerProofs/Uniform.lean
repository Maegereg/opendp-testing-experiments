/-
`sample_uniform_ubig_below` (`rust/src/traits/samplers/uniform/mod.rs`) samples uniformly from
`[0, upper)`: its Proof Definition, proved on the code extracted by Aeneas
(`traits.samplers.uniform.sample_uniform_ubig_below_with`, with the bytes drawn from a uniformly
random tape).

The code draws `L = ⌈bit_len(upper) / 8⌉` bytes, read as a big-endian number `v < 256^L`, until
`v < threshold = max - max % upper` (`max = 256^L - 1`), and returns `v % upper`. Each attempt
returns a given `u < upper` with probability `(threshold / upper) / 256^L` and retries with
probability `(256^L - threshold) / 256^L`, so the loop returns `u` with probability
`(threshold / upper) / threshold = 1 / upper`.
-/
import SamplerProofs.Bytes

open Aeneas Aeneas.Std Result opendp
open scoped ENNReal

namespace OpenDP.Samplers.Uniform

open Classical

abbrev UBig := dashu_int.ubig.UBig
abbrev Res := core.result.Result UBig error.Error

/-- The extracted loop body. -/
def body (upper threshold : UBig) : Body (Tape × alloc.vec.Vec Std.U8) Res := fun p =>
  traits.samplers.uniform.sample_uniform_ubig_below_with_loop.body tapeSource upper threshold
    p.1 p.2

/-- What one iteration does with the bytes `w` it draws. -/
def outcome (upper threshold : UBig) (w : List Std.U8) : ControlFlow (alloc.vec.Vec Std.U8) Res :=
  if h : w.length ≤ Usize.max then
    if beValue w < threshold then .done (.Ok (beValue w % upper))
    else .cont { slice := Slice.from w h }
  else .done (.Ok 0)

/-- One iteration draws as many bytes as the buffer holds. -/
theorem stepP_body {upper threshold : UBig} (hu : upper ≠ 0) (buf : alloc.vec.Vec Std.U8)
    (t : Tape) :
    stepP (Equiv.refl _) (body upper threshold) buf t =
      bindP (draw buf.slice.val.length) (fun w t' => ok (outcome upper threshold w, t')) t := by
  simp [stepP, body, traits.samplers.uniform.sample_uniform_ubig_below_with_loop.body,
    tapeSource, alloc.vec.Vec.deref_mut, alloc.vec.Vec.deref, lift,
    core.result.Result.Insts.CoreOpsTry.branch, dashu_int.convert.UBig.from_be_bytes,
    core.cmp.PartialOrd.lt.trait_default, core.cmp.PartialOrd.lt.default,
    core.cmp.PartialOrd.lt_body, dashu_int.ubig.UBig.Insts.CoreCmpPartialOrdUBig.partial_cmp,
    dashu_int.ubig.UBig.Insts.CoreOpsArithRemSharedRUBigUBig.rem, hu, bindP, draw, outcome,
    alloc.vec.Vec.val, Nat.compare_eq_lt]
  have hl : (t.take (↑buf.slice : List Std.U8).length).length ≤ Usize.max := by simp [Tape.take]
  simp only [hl, ↓reduceDIte]
  split <;> simp

/-- The distribution of one iteration. -/
noncomputable def K (upper threshold : UBig) (buf : alloc.vec.Vec Std.U8)
    (c : ControlFlow (alloc.vec.Vec Std.U8) Res) : ℝ≥0∞ :=
  ∑' w, (if w.length = buf.slice.val.length then (256 : ℝ≥0∞)⁻¹ ^ buf.slice.val.length else 0) *
    (if c = outcome upper threshold w then 1 else 0)

theorem hasDist_step {upper threshold : UBig} (hu : upper ≠ 0) (buf : alloc.vec.Vec Std.U8) :
    HasDist (stepP (Equiv.refl _) (body upper threshold) buf) (K upper threshold buf) := by
  have h := hasDist_bind (hasDist_draw buf.slice.val.length)
    (fun w => hasDist_pure (outcome upper threshold w))
  have e : stepP (Equiv.refl _) (body upper threshold) buf =
      bindP (draw buf.slice.val.length) (fun w t' => ok (outcome upper threshold w, t')) :=
    funext (stepP_body hu buf)
  rw [e]
  exact h

/-! ### The truncated loops -/

section Count

variable (upper threshold : UBig) (L : ℕ)

/-- The probability that `n` iterations from a buffer of length `L` return `b`. -/
noncomputable def C : ℕ → Res → ℝ≥0∞
  | 0, _ => 0
  | n + 1, b => (256 : ℝ≥0∞)⁻¹ ^ L * ∑ v ∈ Finset.range (256 ^ L),
      if v < threshold then (if b = .Ok (v % upper) then 1 else 0) else C n b

end Count

theorem tsum_ite_mul {γ : Type} (o : γ) (M : γ → ℝ≥0∞) :
    (∑' c, (if c = o then (1 : ℝ≥0∞) else 0) * M c) = M o := by
  rw [tsum_eq_single o]
  · simp
  · intro c hc; simp [hc]

theorem loopCut_eq {upper threshold : UBig} {L : ℕ} (hL : L ≤ Usize.max) :
    ∀ n (buf : alloc.vec.Vec Std.U8), buf.slice.val.length = L → ∀ b,
      loopCut (K upper threshold) n buf b = C upper threshold L n b
  | 0, _, _, _ => rfl
  | n + 1, buf, hbuf, b => by
    simp only [loopCut, C, K, hbuf]
    -- Sum over the bytes drawn first.
    simp_rw [← ENNReal.tsum_mul_right, mul_assoc]
    rw [ENNReal.tsum_comm]
    let G : ℕ → ℝ≥0∞ := fun v => (256 : ℝ≥0∞)⁻¹ ^ L *
      (if v < threshold then (if b = .Ok (v % upper) then 1 else 0) else C upper threshold L n b)
    refine Eq.trans (tsum_congr (g := fun w => if w.length = L then G (beValue w) else 0)
      fun w => ?_) ?_
    · rw [ENNReal.tsum_mul_left, tsum_ite_mul]
      by_cases hl : w.length = L
      · simp only [hl, ↓reduceIte, outcome, hL, ↓reduceDIte, G]
        by_cases hv : beValue w < threshold
        · simp only [hv, ↓reduceIte]
        · simp only [hv, ↓reduceIte]
          rw [loopCut_eq hL n _ (by simp [hl]) b]
      · simp [hl]
    · rw [tsum_words G L, Finset.mul_sum]

/-- One more iteration: return `b` now, or retry. -/
theorem C_succ {upper threshold : UBig} {L : ℕ} (hT : threshold ≤ 256 ^ L) (n : ℕ) (b : Res) :
    C upper threshold L (n + 1) b = (256 : ℝ≥0∞)⁻¹ ^ L *
      ((∑ v ∈ Finset.range threshold, if b = .Ok (v % upper) then 1 else 0) +
        ((256 ^ L - threshold : ℕ) : ℝ≥0∞) * C upper threshold L n b) := by
  rw [C]
  congr 1
  rw [← Finset.sum_range_add_sum_Ico _ hT]
  congr 1
  · exact Finset.sum_congr rfl fun v hv => by simp [Finset.mem_range.mp hv]
  · rw [Finset.sum_congr rfl (g := fun _ => C upper threshold L n b) fun v hv => by
      simp [not_lt.mpr (Finset.mem_Ico.mp hv).1]]
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/-- Closed form of the truncations: `C n b = P ∑_{k<n} Q^k`, where `P` is the probability that
one iteration returns `b` and `Q` the probability that it retries. -/
theorem C_eq {upper threshold : UBig} {L : ℕ} (hT : threshold ≤ 256 ^ L) (b : Res) :
    ∀ n, C upper threshold L n b =
      ((256 : ℝ≥0∞)⁻¹ ^ L * ∑ v ∈ Finset.range threshold,
        if b = .Ok (v % upper) then 1 else 0) *
      ∑ k ∈ Finset.range n, ((256 : ℝ≥0∞)⁻¹ ^ L * ((256 ^ L - threshold : ℕ) : ℝ≥0∞)) ^ k
  | 0 => by simp [C]
  | n + 1 => by
    rw [C_succ hT, C_eq hT b n]
    have hS : ∀ Q : ℝ≥0∞, ∑ k ∈ Finset.range (n + 1), Q ^ k =
        1 + Q * ∑ k ∈ Finset.range n, Q ^ k := by
      intro Q
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
      simp [pow_succ']
    rw [hS]
    ring

/-! ### Arithmetic facts about the code's constants -/

theorem beValue_replicate_max : ∀ L, beValue (List.replicate L core.num.U8.MAX) = 256 ^ L - 1
  | 0 => by simp [beValue]
  | L + 1 => by
    rw [List.replicate_succ, beValue_cons, beValue_replicate_max L, List.length_replicate]
    have h1 : 1 ≤ 256 ^ L := Nat.one_le_pow _ _ (by norm_num)
    have : core.num.U8.MAX.val = 255 := by simp [core.num.U8.MAX, U8.rMax]
    rw [this, pow_succ]
    omega

/-- The number of values below `threshold` with a given remainder. -/
theorem sum_mod (upper q u : ℕ) (hu : u < upper) :
    (∑ v ∈ Finset.range (upper * q), if u = v % upper then (1 : ℝ≥0∞) else 0) = q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Nat.cast_succ]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp [Nat.mod_eq_of_lt hu]
    · intro v hv hne
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hv)]
      simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.mpr hu) h

/-- The limit of the truncations: `(q / A) / (1 - (A - T) / A) = q / T = 1 / upper`. -/
theorem geometric_limit {A upper q : ℕ} (hA : 1 ≤ A) (hT : upper * q ≤ A) (hq : 1 ≤ q)
    (hu : 0 < upper) :
    ((A : ℝ≥0∞)⁻¹ * q) * (1 - (A : ℝ≥0∞)⁻¹ * ((A - upper * q : ℕ) : ℝ≥0∞))⁻¹ =
      (upper : ℝ≥0∞)⁻¹ := by
  have ha0 : (A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
  have haT : (A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top A
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hu0 : (upper : ℝ≥0∞) ≠ 0 := by exact_mod_cast hu.ne'
  have ht0 : ((upper * q : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero hu.ne' (by omega))
  have htA : ((upper * q : ℕ) : ℝ≥0∞) ≤ A := Nat.cast_le.mpr hT
  have hsub : (A : ℝ≥0∞)⁻¹ * ((A - upper * q : ℕ) : ℝ≥0∞) =
      1 - (A : ℝ≥0∞)⁻¹ * ((upper * q : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.natCast_sub, ENNReal.mul_sub (fun _ _ => ENNReal.inv_ne_top.mpr ha0),
      ENNReal.inv_mul_cancel ha0 haT]
  have hle : (A : ℝ≥0∞)⁻¹ * ((upper * q : ℕ) : ℝ≥0∞) ≤ 1 := by
    calc (A : ℝ≥0∞)⁻¹ * ((upper * q : ℕ) : ℝ≥0∞) ≤ (A : ℝ≥0∞)⁻¹ * A := by gcongr
      _ = 1 := ENNReal.inv_mul_cancel ha0 haT
  rw [hsub, ENNReal.sub_sub_cancel ENNReal.one_ne_top hle,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr ht0), inv_inv]
  calc (A : ℝ≥0∞)⁻¹ * q * (A * ((upper * q : ℕ) : ℝ≥0∞)⁻¹)
      = ((A : ℝ≥0∞)⁻¹ * A) * (q * ((upper * q : ℕ) : ℝ≥0∞)⁻¹) := by ring
    _ = q * ((upper * q : ℕ) : ℝ≥0∞)⁻¹ := by rw [ENNReal.inv_mul_cancel ha0 haT, one_mul]
    _ = q * ((upper : ℝ≥0∞)⁻¹ * (q : ℝ≥0∞)⁻¹) := by
        rw [Nat.cast_mul, ENNReal.mul_inv (Or.inl hu0) (Or.inl (ENNReal.natCast_ne_top _))]
    _ = (upper : ℝ≥0∞)⁻¹ * ((q : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹) := by ring
    _ = (upper : ℝ≥0∞)⁻¹ := by rw [ENNReal.mul_inv_cancel hq0 (ENNReal.natCast_ne_top _), mul_one]

/-! ### The theorem -/

/-- The uniform distribution on `[0, upper)` (the samplers never return an error). -/
noncomputable def uniform (upper : UBig) : Res → ℝ≥0∞
  | .Ok u => if u < upper then (upper : ℝ≥0∞)⁻¹ else 0
  | .Err _ => 0

/-- **`sample_uniform_ubig_below` samples uniformly from `[0, upper)`**, for `upper > 0` whose
bit length fits in a `usize`. -/
theorem sample_uniform_ubig_below_with_uniform (upper : UBig) (hu : 0 < upper)
    (hs : Nat.size upper < 2 ^ UScalarTy.Usize.numBits) :
    HasDist (fun t => traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t upper)
      (uniform upper) := by
  -- The constants.
  obtain ⟨L, hLdef⟩ : ∃ L, L = (Nat.size upper + 7) / 8 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 256 ^ L := ⟨_, rfl⟩
  obtain ⟨mx, hmx⟩ : ∃ m, m = A - 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = mx / upper := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = mx - mx % upper := ⟨_, rfl⟩
  have hsize : 1 ≤ Nat.size upper := Nat.size_pos.mpr hu
  have hLs : L ≤ Nat.size upper := by omega
  have hL : L < 2 ^ UScalarTy.Usize.numBits := lt_of_le_of_lt hLs hs
  have hLmax : L ≤ Usize.max := by
    have : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
      rw [Usize.max_def]; simp [UScalarTy.numBits, Usize.numBits]
    omega
  have hApos : 1 ≤ A := hA ▸ Nat.one_le_pow _ _ (by norm_num)
  have hupA : upper < A := by
    calc upper < 2 ^ Nat.size upper := Nat.lt_size_self upper
      _ ≤ 2 ^ (8 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = A := by rw [hA, pow_mul]; norm_num
  have hTq : T = upper * q := by
    have := Nat.mod_add_div mx upper
    rw [← hq] at this
    omega
  have hupmx : upper ≤ mx := by rw [hmx]; exact Nat.le_sub_one_of_lt hupA
  have hq1 : 1 ≤ q := by rw [hq]; exact (Nat.one_le_div_iff hu).mpr hupmx
  have hTA : T ≤ A := by omega
  have hTpos : 1 ≤ T := by rw [hTq]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- The code is the loop, from a buffer of `L` zeros.
  let buf0 : alloc.vec.Vec Std.U8 := { slice := Slice.from (List.replicate L 0#u8) (by simpa) }
  have hcode : (fun t => traits.samplers.uniform.sample_uniform_ubig_below_with tapeSource t upper) =
      loopP (Equiv.refl _) (body upper T) buf0 := by
    funext t
    have hclone : ∀ l : List Std.U8,
        List.clone (liftFun1 core.clone.impls.CloneU8.clone) l = ok ⟨l, rfl⟩ := by
      intro l
      induction l with
      | nil => simp [List.clone, List.mapM_with_length, pure]
      | cons a l ih =>
        simp only [List.clone] at ih ⊢
        simp [List.mapM_with_length, ih, liftFun1, core.clone.impls.CloneU8.clone, pure]
    have hs' : Nat.size upper < 2 ^ System.Platform.numBits := by
      simpa [UScalarTy.numBits] using hs
    have hL' : (Nat.size upper + 7) / 8 < 2 ^ System.Platform.numBits := by
      simpa [UScalarTy.numBits, hLdef] using hL
    subst hT hmx hA hLdef
    simp [traits.samplers.uniform.sample_uniform_ubig_below_with,
      dashu_int.ubig.UBig.Insts.Dashu_baseBitBitTest.bit_len, usizeOfNat,
      core.num.Usize.div_ceil, alloc.vec.from_elem, alloc.vec.Vec.deref,
      dashu_int.convert.UBig.from_be_bytes, SharedLUBig.Insts.CoreOpsArithRemSharedRUBigUBig.rem,
      SharedLUBig.Insts.CoreOpsArithSubUBigUBig.sub, hs', hL', hclone, hu.ne', Usize.ofNatCore_val_eq,
      alloc.vec.Vec.val, Nat.mod_le, beValue_replicate_max,
      traits.samplers.uniform.sample_uniform_ubig_below_with_loop, loopP, alloc.vec.Vec.from,
      Slice.from_val]
    rfl
  rw [hcode]
  have hdist := hasDist_loop (hasDist_step (threshold := T) hu.ne') buf0
  refine ⟨hdist.1, fun b => ?_⟩
  rw [hdist.2 b]
  have hbuf0 : buf0.slice.val.length = L := by
    simp only [buf0, Slice.from_val, List.length_replicate]
  have hTA' : T ≤ 256 ^ L := hA ▸ hTA
  simp_rw [loopCut_eq hLmax _ buf0 hbuf0, C_eq hTA']
  rw [← ENNReal.mul_iSup, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]
  have hinv : (256 : ℝ≥0∞)⁻¹ ^ L = ((A : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [hA, ← ENNReal.inv_pow, Nat.cast_pow]; norm_num
  rw [hinv, ← hA]
  rcases b with u | e
  · simp only [uniform, core.result.Result.Ok.injEq]
    by_cases hlt : u < upper
    · simp only [hlt, ↓reduceIte]
      rw [hTq, sum_mod upper q u hlt]
      exact geometric_limit hApos (hTq ▸ hTA) hq1 hu
    · simp only [hlt, ↓reduceIte]
      rw [Finset.sum_eq_zero fun v _ => by
        simp only [ite_eq_right_iff, one_ne_zero, imp_false]
        intro h; exact hlt (h ▸ Nat.mod_lt v hu)]
      simp
  · simp [uniform]

end OpenDP.Samplers.Uniform
