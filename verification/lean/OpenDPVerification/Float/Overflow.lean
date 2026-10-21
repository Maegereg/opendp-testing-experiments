/-
Soundness of `can_float_sum_overflow` (`rust/src/transformations/sum/float/checked/mod.rs`).

`CanFloatSumOverflow::can_float_sum_overflow(size, (lower, upper))` returns `Ok(false)` to claim
that summing at most `size` values within `[lower, upper]` cannot overflow, with
`Sequential::<T>::unchecked_sum` and `Pairwise::<T>::unchecked_sum` respectively. The
transformations rely on this claim: they then sum without checking for infinities.

`canOverflowSeq` and `canOverflowPw` transcribe the two implementations line by line, over the
reals. The primitives they call (`inf_cast`, `neg_inf_div`, `inf_mul`, `powf`,
`round_up_to_nearest_power_of_two`) are left abstract: `Prims.Spec` only assumes their trusted
contracts, so the theorems hold for every implementation meeting them.
-/
import OpenDPVerification.Float.Sum

namespace OpenDP.Float

namespace Fmt

/-- The primitives called by `can_float_sum_overflow`, on values of type `T`. `none` is `Err`. -/
structure Prims (φ : Fmt) where
  /-- `T::inf_cast(size)` -/
  infCast : ℕ → Option ℝ
  /-- `a.neg_inf_div(&b)` -/
  negInfDiv : ℝ → ℝ → Option ℝ
  /-- `a.inf_mul(&b)` -/
  infMul : ℝ → ℝ → Option ℝ
  /-- `_2.powf(T::exact_int_cast(k)?)`, where `_2 = T::one() + T::one()` is exactly 2 -/
  powf2 : ℤ → ℝ
  /-- `round_up_to_nearest_power_of_two(x)` -/
  roundUpPow2 : ℝ → Option ℝ

/-- The contracts of the primitives that the soundness proof relies on. -/
structure Prims.Spec {φ : Fmt} (P : Prims φ) : Prop where
  /-- `InfCast` proof definition: the result is at least the input. -/
  infCast : ∀ n v, P.infCast n = some v → (n : ℝ) ≤ v
  /-- `InfDiv` proof definition: the result is at most the quotient. -/
  negInfDiv : ∀ a b v, 0 < b → P.negInfDiv a b = some v → v ≤ a / b
  /-- `InfMul` proof definition (the result is at least the product), and the result is finite.
  Finiteness is not part of the proof definition, but the float implementations check it, and
  the overflow check depends on it: an `Ok(inf)` would satisfy the proof definition. -/
  infMul : ∀ a b v, P.infMul a b = some v → a * b ≤ v ∧ v ≤ φ.maxFinite
  /-- `powf` does not overestimate powers of two. The platform `pow` is exact on them. -/
  powf2 : ∀ k : ℤ, P.powf2 k ≤ 2 ^ k
  /-- `round_up_to_nearest_power_of_two` on a non-negative float returns a value at least as
  large as a power of two `2 ^ c ≥ x`, with `c ≥ -emax` (`2 ^ (raw_exponent - bias)`, plus one
  when the mantissa is nonzero, rounded up by `inf_powi`). -/
  roundUpPow2 : ∀ x v, 0 ≤ x → P.roundUpPow2 x = some v →
    ∃ c : ℤ, φ.qmin ≤ c ∧ x ≤ 2 ^ c ∧ 2 ^ c ≤ v

variable {φ : Fmt}

/-- `<Sequential<T> as CanFloatSumOverflow>::can_float_sum_overflow`. -/
noncomputable def canOverflowSeq (P : Prims φ) (size : ℕ) (lower upper : ℝ) : Option Bool := do
  let size_ ← P.infCast size
  let mag := max |lower| upper
  -- `T::EXPONENT_BIAS - T::MANTISSA_BITS - T::Bits::one()`, with `MANTISSA_BITS = p - 1`
  let magLimit := P.powf2 (φ.emax - (φ.p - 1) - 1)
  if mag < magLimit then return false
  let M ← P.roundUpPow2 mag
  return (P.infMul M size_).isNone

/-- `<Pairwise<T> as CanFloatSumOverflow>::can_float_sum_overflow`. -/
noncomputable def canOverflowPw (P : Prims φ) (size : ℕ) (lower upper : ℝ) : Option Bool := do
  let size_ ← P.infCast size
  let mag := max |lower| upper
  -- `T::EXPONENT_BIAS - T::MANTISSA_BITS`
  let maxUlp := P.powf2 (φ.emax - (φ.p - 1))
  let magLimit ← P.negInfDiv maxUlp size_
  if mag < magLimit then return false
  let M ← P.roundUpPow2 mag
  return (P.infMul M size_).isNone

/-- The second check, shared by both implementations: `RU(mag) * size` is finite. -/
theorem check2 {P : Prims φ} (hP : P.Spec) {size : ℕ} {sz mag M v : ℝ} (hsz : (size : ℝ) ≤ sz)
    (hmag : 0 ≤ mag) (hM : P.roundUpPow2 mag = some M) (hv : P.infMul M sz = some v) :
    ∃ c : ℤ, φ.qmin ≤ c ∧ mag ≤ 2 ^ c ∧ (size : ℝ) * 2 ^ c ≤ φ.maxFinite := by
  obtain ⟨c, hc, hmc, hcM⟩ := hP.roundUpPow2 _ _ hmag hM
  obtain ⟨h1, h2⟩ := hP.infMul _ _ _ hv
  refine ⟨c, hc, hmc, ?_⟩
  have := two_zpow_pos c
  calc (size : ℝ) * 2 ^ c ≤ sz * M := by
        gcongr
        · exact le_trans (by positivity) hsz
    _ = M * sz := mul_comm _ _
    _ ≤ φ.maxFinite := h1.trans h2

/-- **Soundness of the sequential overflow check.** If `can_float_sum_overflow` returns
`Ok(false)`, then the sequential sum of any dataset of at most `size` values within the bounds
is finite. -/
theorem canOverflowSeq_sound {P : Prims φ} (hP : P.Spec) {size : ℕ} {lower upper : ℝ}
    (h : canOverflowSeq P size lower upper = some false) {xs : List ℝ} (hlen : xs.length ≤ size)
    (hx : ∀ x ∈ xs, lower ≤ x ∧ x ≤ upper) : φ.seqSum xs ≠ none := by
  have hxm : ∀ x ∈ xs, |x| ≤ max |lower| upper := fun x hx' => abs_le_of_mem_bounds (hx x hx')
  have hmag : 0 ≤ max |lower| upper := le_max_of_le_left (abs_nonneg _)
  unfold canOverflowSeq at h
  cases hsz : P.infCast size with
  | none => simp [hsz] at h
  | some sz =>
  simp only [hsz, Option.bind_eq_bind, Option.bind_some] at h
  split_ifs at h with hlim
  · -- check 1: every value is below half an ulp of the largest finite value
    apply seqSum_ne_none_of_small
    intro x hxs
    have hpow := hP.powf2 (φ.emax - (φ.p - 1) - 1)
    have e : (2 : ℝ) ^ (φ.emax - (φ.p - 1) - 1) = 2 ^ φ.qtop / 2 := by
      rw [show φ.emax - ((φ.p : ℤ) - 1) - 1 = φ.qtop - 1 by unfold qtop; ring,
        zpow_sub_one₀ (by norm_num)]; ring
    linarith [hxm x hxs]
  · -- check 2
    cases hM : P.roundUpPow2 (max |lower| upper) with
    | none => simp [hM] at h
    | some M =>
    cases hv : P.infMul M sz with
    | none => simp [hM, hv] at h
    | some v =>
    obtain ⟨c, hc, hmc, hn⟩ := check2 hP (hP.infCast _ _ hsz) hmag hM hv
    exact seqSum_ne_none_of_mul hc hn hlen (fun x hxs => (hxm x hxs).trans hmc)

/-- The first pairwise check gives the second, with `M` the next power of two above `mag`.
Sizes are `usize` values, below `2 ^ 64`. -/
theorem check1_pw {size : ℕ} {mag : ℝ} (hsize : size < 2 ^ 64)
    (hfmt : (2 : ℝ) ^ 64 * 2 ^ φ.qmin ≤ φ.maxFinite) (h : mag * size < 2 ^ φ.qtop) :
    ∃ c : ℤ, φ.qmin ≤ c ∧ mag ≤ 2 ^ c ∧ (size : ℝ) * 2 ^ c ≤ φ.maxFinite := by
  have hsize' : (size : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hsize.le
  rcases le_or_gt mag (2 ^ φ.qmin) with hsmall | hbig
  · exact ⟨φ.qmin, le_rfl, hsmall, le_trans (by gcongr) hfmt⟩
  · have hpos : 0 < mag := lt_trans (two_zpow_pos _) hbig
    set c := Int.clog 2 mag
    have hup : mag ≤ 2 ^ c := by
      have := Int.self_le_zpow_clog (b := 2) (by norm_num) mag; exact_mod_cast this
    have hlow : (2 : ℝ) ^ (c - 1) < mag := by
      have := Int.zpow_pred_clog_lt_self (b := 2) (by norm_num) hpos; exact_mod_cast this
    have hc : φ.qmin ≤ c := by
      have := hbig.trans_le hup
      exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this).le
    refine ⟨c, hc, hup, ?_⟩
    rw [zpow_sub_one₀ (by norm_num)] at hlow
    have h4 := two_pow_p_ge (φ := φ)
    have ht := two_zpow_pos φ.qtop
    have hs : (0 : ℝ) ≤ size := Nat.cast_nonneg _
    calc (size : ℝ) * 2 ^ c ≤ size * (2 * mag) := by gcongr; linarith
      _ = 2 * (mag * size) := by ring
      _ ≤ 2 * 2 ^ φ.qtop := by linarith
      _ ≤ φ.maxFinite := by rw [maxFinite]; nlinarith

/-- **Soundness of the pairwise overflow check.** If `can_float_sum_overflow` returns
`Ok(false)`, then the pairwise sum of any dataset of at most `size` values within the bounds is
finite. -/
theorem canOverflowPw_sound {P : Prims φ} (hP : P.Spec) {size : ℕ} (hsize : size < 2 ^ 64)
    (hfmt : (2 : ℝ) ^ 64 * 2 ^ φ.qmin ≤ φ.maxFinite) {lower upper : ℝ}
    (h : canOverflowPw P size lower upper = some false) {xs : List ℝ} (hlen : xs.length ≤ size)
    (hx : ∀ x ∈ xs, lower ≤ x ∧ x ≤ upper) : φ.pwSum xs ≠ none := by
  have hxm : ∀ x ∈ xs, |x| ≤ max |lower| upper := fun x hx' => abs_le_of_mem_bounds (hx x hx')
  have hmag : 0 ≤ max |lower| upper := le_max_of_le_left (abs_nonneg _)
  -- an empty dataset sums to zero
  rcases Nat.eq_zero_or_pos size with rfl | hsize0
  · rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)]; simp [pwSum]
  unfold canOverflowPw at h
  cases hsz : P.infCast size with
  | none => simp [hsz] at h
  | some sz =>
  have hszge := hP.infCast _ _ hsz
  have hszpos : 0 < sz := lt_of_lt_of_le (by exact_mod_cast hsize0) hszge
  cases hlim : P.negInfDiv (P.powf2 (φ.emax - (φ.p - 1))) sz with
  | none => simp [hsz, hlim] at h
  | some lim =>
  simp only [hsz, hlim, Option.bind_eq_bind, Option.bind_some] at h
  split_ifs at h with hlt
  · -- check 1: `mag * size < ulp(maxFinite)`
    obtain ⟨c, hc, hmc, hn⟩ : ∃ c : ℤ, φ.qmin ≤ c ∧ max |lower| upper ≤ 2 ^ c ∧
        (size : ℝ) * 2 ^ c ≤ φ.maxFinite := by
      apply check1_pw hsize hfmt
      have h1 := hP.negInfDiv _ _ _ hszpos hlim
      have h2 := hP.powf2 (φ.emax - (φ.p - 1))
      have e : (2 : ℝ) ^ (φ.emax - ((φ.p : ℤ) - 1)) = 2 ^ φ.qtop := by
        congr 1; unfold qtop; ring
      rw [e] at h2
      have : max |lower| upper * sz < 2 ^ φ.qtop := by
        rw [← lt_div_iff₀ hszpos]
        exact lt_of_lt_of_le hlt (h1.trans (div_le_div_of_nonneg_right h2 hszpos.le))
      calc max |lower| upper * size ≤ max |lower| upper * sz := by gcongr
        _ < 2 ^ φ.qtop := this
    exact pwSum_ne_none_of_mul hc hn hlen (fun x hxs => (hxm x hxs).trans hmc)
  · -- check 2
    cases hM : P.roundUpPow2 (max |lower| upper) with
    | none => simp [hM] at h
    | some M =>
    cases hv : P.infMul M sz with
    | none => simp [hM, hv] at h
    | some v =>
    obtain ⟨c, hc, hmc, hn⟩ := check2 hP hszge hmag hM hv
    exact pwSum_ne_none_of_mul hc hn hlen (fun x hxs => (hxm x hxs).trans hmc)

end Fmt

/-- `f64`: IEEE 754 binary64. -/
def binary64 : Fmt := ⟨53, 1023, by norm_num, by norm_num⟩

/-- `f32`: IEEE 754 binary32. -/
def binary32 : Fmt := ⟨24, 127, by norm_num, by norm_num⟩

/-- The side condition of `canOverflowPw_sound` holds in formats wide enough to scale any `usize`
size by the smallest subnormal without overflowing. -/
theorem Fmt.fmt_of {φ : Fmt} (h1 : φ.qmin + 64 ≤ 0) (h2 : 0 ≤ φ.qtop) :
    (2 : ℝ) ^ 64 * 2 ^ φ.qmin ≤ φ.maxFinite := by
  have h4 := Fmt.two_pow_p_ge (φ := φ)
  calc (2 : ℝ) ^ 64 * 2 ^ φ.qmin = 2 ^ (φ.qmin + 64) := by
        rw [zpow_add₀ (by norm_num), mul_comm]; norm_cast
    _ ≤ 2 ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) h1
    _ = 1 * 1 := by norm_num
    _ ≤ (2 ^ φ.p - 1) * 2 ^ φ.qtop := by
        exact mul_le_mul (by linarith) (one_le_zpow₀ (by norm_num) h2) (by norm_num) (by linarith)

theorem binary64_fmt : (2 : ℝ) ^ 64 * 2 ^ binary64.qmin ≤ binary64.maxFinite :=
  Fmt.fmt_of (by decide) (by decide)

theorem binary32_fmt : (2 : ℝ) ^ 64 * 2 ^ binary32.qmin ≤ binary32.maxFinite :=
  Fmt.fmt_of (by decide) (by decide)

/-- `f64::MAX` -/
example : binary64.maxFinite = (2 ^ 53 - 1) * 2 ^ 971 := by
  simp only [Fmt.maxFinite, Fmt.qtop, binary64]; norm_num

/-- `f32::MAX` -/
example : binary32.maxFinite = (2 ^ 24 - 1) * 2 ^ 104 := by
  simp only [Fmt.maxFinite, Fmt.qtop, binary32]; norm_num

end OpenDP.Float
