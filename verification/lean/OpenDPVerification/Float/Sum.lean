/-
Floating-point sequential and pairwise summation, and sufficient conditions for them not to
overflow.

Both arguments reduce an arbitrary dataset bounded by `M = 2 ^ c` to the dataset of all `M`s,
by monotonicity of rounding, and then bound the floating-point sum of `k` copies of `M`:

* sequential: exactly `min(k, 2 ^ p) * M`. Past `2 ^ p * M` the sum stagnates, because
  `2 ^ p * M + M` is a tie that rounds to even, that is, down (`seq_step`). This needs ties to
  even: with ties rounded up the sum keeps growing, and overflows.
* pairwise: at most `RU(k) * M`, where `RU` rounds up to the format (`ruN_add`).

Either way, the sum does not overflow when `n * M` does not exceed the largest finite value.
-/
import OpenDPVerification.Float.Format

namespace OpenDP.Float

namespace Fmt

variable (φ : Fmt)

/-- IEEE addition: `none` when the result overflows to an infinity. Once a sum overflows, it
stays infinite or becomes NaN, so a sum is finite exactly when no addition overflows. -/
noncomputable def fadd (a b : ℝ) : Option ℝ :=
  if |φ.rne (a + b)| ≤ φ.maxFinite then some (φ.rne (a + b)) else none

/-- Sequential summation, `Sequential::<T>::unchecked_sum`: `arg.iter().cloned().sum()`. -/
noncomputable def seqSum (xs : List ℝ) : Option ℝ := xs.foldlM φ.fadd 0

/-- Pairwise summation, `Pairwise::<T>::unchecked_sum`. -/
noncomputable def pwSum : List ℝ → Option ℝ
  | [] => some 0
  | [x] => some x
  | x :: y :: rest => do
    let a ← pwSum ((x :: y :: rest).take ((rest.length + 2) / 2))
    let b ← pwSum ((x :: y :: rest).drop ((rest.length + 2) / 2))
    φ.fadd a b
termination_by xs => xs.length
decreasing_by all_goals (simp only [List.length_take, List.length_drop, List.length_cons]; omega)

/-- Natural numbers of the format (with unbounded exponent range). -/
def IsRepN (k : ℕ) : Prop := ∃ m q : ℕ, m ≤ 2 ^ φ.p ∧ k = m * 2 ^ q

theorem exists_isRepN_ge (k : ℕ) : ∃ y, k ≤ y ∧ φ.IsRepN y :=
  ⟨2 ^ k, Nat.lt_two_pow_self.le, 1, k, Nat.one_le_two_pow, by ring⟩

open Classical in
/-- Round a natural number up to the format. -/
noncomputable def ruN (k : ℕ) : ℕ := Nat.find (φ.exists_isRepN_ge k)

variable {φ}

theorem isRepN_of_le {k : ℕ} (h : k ≤ 2 ^ φ.p) : φ.IsRepN k := ⟨k, 0, h, by simp⟩

theorem isRepN_half {t : ℕ} (h : φ.IsRepN (2 * t)) : φ.IsRepN t := by
  obtain ⟨m, q, hm, he⟩ := h
  rcases q with _ | q
  · exact isRepN_of_le (by simp at he; omega)
  · refine ⟨m, q, hm, ?_⟩
    rw [pow_succ] at he
    linarith

theorem isRepN_odd {y : ℕ} (h : φ.IsRepN y) (ho : y % 2 = 1) : y ≤ 2 ^ φ.p := by
  obtain ⟨m, q, hm, rfl⟩ := h
  rcases q with _ | q
  · simpa using hm
  · rw [pow_succ, ← mul_assoc, Nat.mul_mod_left] at ho
    omega

theorem ruN_spec (k : ℕ) : k ≤ φ.ruN k ∧ φ.IsRepN (φ.ruN k) := by
  classical
  unfold ruN; convert Nat.find_spec (φ.exists_isRepN_ge k)

theorem ruN_le {k y : ℕ} (hk : k ≤ y) (hy : φ.IsRepN y) : φ.ruN k ≤ y := by
  classical
  unfold ruN; convert Nat.find_min' (φ.exists_isRepN_ge k) ⟨hk, hy⟩

theorem ruN_mono {k l : ℕ} (h : k ≤ l) : φ.ruN k ≤ φ.ruN l :=
  ruN_le (h.trans (ruN_spec l).1) (ruN_spec l).2

/-- Rounding up the sizes of the two halves of a pairwise sum: the key step of the pairwise
bound. When `a + b` rounds up to an even `y`, both halves fit under `y / 2`, which is in the
format; when it rounds up to an odd `y`, `y ≤ 2 ^ p`, so nothing is rounded. -/
theorem ruN_add {a b : ℕ} (hb : b = a ∨ b = a + 1) : φ.ruN a + φ.ruN b ≤ φ.ruN (a + b) := by
  obtain ⟨hy1, hy2⟩ := ruN_spec (φ := φ) (a + b)
  rcases Nat.even_or_odd (φ.ruN (a + b)) with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hrep : φ.IsRepN t := isRepN_half (by rw [two_mul, ← ht]; exact hy2)
    have ha : φ.ruN a ≤ t := ruN_le (by omega) hrep
    have hb' : φ.ruN b ≤ t := ruN_le (by omega) hrep
    omega
  · have := isRepN_odd hy2 (by omega)
    have ha := ruN_le (φ := φ) (le_refl a) (isRepN_of_le (by omega))
    have hb' := ruN_le (φ := φ) (le_refl b) (isRepN_of_le (by omega))
    omega

theorem isRep_of_isRepN {k : ℕ} {c : ℤ} (hk : φ.IsRepN k) (hc : φ.qmin ≤ c) :
    φ.IsRep (k * (2 : ℝ) ^ c) := by
  obtain ⟨m, q, hm, rfl⟩ := hk
  refine ⟨m, q + c, by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hm, by omega, ?_⟩
  push_cast
  rw [zpow_add₀ (by norm_num), zpow_natCast]; ring

/-- If `n * 2 ^ c` is at most the largest finite value, so is `RU(n) * 2 ^ c`. -/
theorem ruN_mul_le {n : ℕ} {c : ℤ} (hn : (n : ℝ) * 2 ^ c ≤ φ.maxFinite) :
    (φ.ruN n : ℝ) * 2 ^ c ≤ φ.maxFinite := by
  have hc0 := two_zpow_pos c
  have h1 : (1 : ℕ) ≤ 2 ^ φ.p := Nat.one_le_two_pow
  rcases le_or_gt c φ.qtop with h | h
  · -- `maxFinite = N * 2 ^ c` with `N` in the format
    set N := (2 ^ φ.p - 1) * 2 ^ (φ.qtop - c).toNat
    have e : (2 : ℝ) ^ ((φ.qtop - c).toNat) * 2 ^ c = 2 ^ φ.qtop := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; congr 1; omega
    have hN : (N : ℝ) * 2 ^ c = φ.maxFinite := by
      simp only [N, maxFinite]
      push_cast [Nat.cast_sub h1]
      rw [mul_assoc, e]
    have hnN : n ≤ N := by
      have : (n : ℝ) ≤ N := le_of_mul_le_mul_right (hN ▸ hn) hc0
      exact_mod_cast this
    have := ruN_le hnN ⟨2 ^ φ.p - 1, (φ.qtop - c).toNat, Nat.sub_le _ _, rfl⟩
    calc (φ.ruN n : ℝ) * 2 ^ c ≤ N * 2 ^ c := by gcongr
      _ = φ.maxFinite := hN
  · -- `n < 2 ^ p`, so `n` is in the format
    have hlt : (n : ℝ) < 2 ^ φ.p := by
      have : φ.maxFinite < 2 ^ φ.p * 2 ^ c := by
        rw [maxFinite]
        calc ((2 : ℝ) ^ φ.p - 1) * 2 ^ φ.qtop < 2 ^ φ.p * 2 ^ φ.qtop := by
              gcongr; linarith
          _ ≤ 2 ^ φ.p * 2 ^ c :=
            mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) h.le) (by positivity)
      exact lt_of_mul_lt_mul_right (hn.trans_lt this) hc0.le
    have : n ≤ 2 ^ φ.p := by exact_mod_cast hlt.le
    have := ruN_le (le_refl n) (isRepN_of_le (φ := φ) this)
    have := (ruN_spec (φ := φ) n).1
    rw [show φ.ruN n = n by omega]; exact hn

theorem abs_le_of_mem_bounds {L U x : ℝ} (h : L ≤ x ∧ x ≤ U) : |x| ≤ max |L| U := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact le_max_of_le_right h.2
  · rw [abs_of_neg hx]; exact le_max_of_le_left (le_trans (by linarith) (neg_le_abs L))

/-! ### Sequential summation -/

/-- `rne ((2 ^ p + 1) * 2 ^ c) = 2 ^ p * 2 ^ c`: a tie, rounded to the even neighbour. -/
theorem rne_tie {c : ℤ} (hc : φ.qmin ≤ c) :
    φ.rne ((2 ^ φ.p + 1) * 2 ^ c) = 2 ^ φ.p * 2 ^ c := by
  obtain ⟨p', hp'⟩ : ∃ p', φ.p = p' + 1 := ⟨φ.p - 1, by have := φ.hp; omega⟩
  have hp'1 : p' ≠ 0 := by have := φ.hp; omega
  have hc0 := two_zpow_pos c
  have h4 := two_pow_p_ge (φ := φ)
  have hx : 0 < ((2 : ℝ) ^ φ.p + 1) * 2 ^ c := by positivity
  have hpc : (2 : ℝ) ^ (c + φ.p) = 2 ^ φ.p * 2 ^ c := by
    rw [zpow_add₀ (by norm_num), zpow_natCast, mul_comm]
  have hf : φ.fexp (((2 : ℝ) ^ φ.p + 1) * 2 ^ c) = c + 1 := by
    have h1 : (2 : ℝ) ^ (c + φ.p) ≤ |((2 : ℝ) ^ φ.p + 1) * 2 ^ c| := by
      rw [abs_of_pos hx, hpc]; nlinarith
    have h2 : |((2 : ℝ) ^ φ.p + 1) * 2 ^ c| < 2 ^ (c + φ.p + 1) := by
      rw [abs_of_pos hx, zpow_add_one₀ (by norm_num), hpc]; nlinarith
    rw [fexp_of_bounds h1 h2 (by omega)]; ring
  unfold rne
  rw [hf, zpow_add_one₀ (by norm_num)]
  have hy : ((2 : ℝ) ^ φ.p + 1) * 2 ^ c / (2 ^ c * 2) = (2 ^ p' : ℤ) + 1 / 2 := by
    rw [hp', pow_succ]; push_cast; field_simp
  have hr : roundEven (((2 : ℝ) ^ φ.p + 1) * 2 ^ c / (2 ^ c * 2)) = 2 ^ p' := by
    rw [hy]
    exact roundEven_eq (Or.inr ⟨by norm_num, Int.even_pow.mpr ⟨even_two, hp'1⟩⟩)
  rw [hr, hp', pow_succ]; push_cast; ring

/-- One step of the sequential bound: after `k` additions of values bounded by `M = 2 ^ c`,
the sum is bounded by `min(k, 2 ^ p) * M`. -/
theorem seq_step {c : ℤ} (hc : φ.qmin ≤ c) {k : ℕ} {y : ℝ}
    (hy : |y| ≤ (min k (2 ^ φ.p) : ℕ) * 2 ^ c + 2 ^ c) :
    |φ.rne y| ≤ (min (k + 1) (2 ^ φ.p) : ℕ) * 2 ^ c := by
  rcases lt_or_ge k (2 ^ φ.p) with h | h
  · rw [min_eq_left h.le] at hy
    rw [min_eq_left (by omega)]
    have hrep := isRep_of_mul (φ := φ) (k := (k + 1 : ℕ)) (e := c)
      (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast h) hc
    push_cast at hrep ⊢
    exact abs_rne_le hrep (by linarith)
  · rw [min_eq_right h] at hy
    rw [min_eq_right (by omega)]
    push_cast at hy ⊢
    have hB : |y| ≤ (2 ^ φ.p + 1) * 2 ^ c := by linarith
    rw [abs_le] at hB ⊢
    constructor
    · have := rne_mono (φ := φ) hB.1
      rw [rne_neg, rne_tie hc] at this
      linarith
    · have := rne_mono (φ := φ) hB.2
      rw [rne_tie hc] at this; exact this

theorem foldlM_seq_bound {c : ℤ} (hc : φ.qmin ≤ c) :
    ∀ (xs : List ℝ) (k : ℕ) (s : ℝ), (∀ x ∈ xs, |x| ≤ 2 ^ c) →
      |s| ≤ (min k (2 ^ φ.p) : ℕ) * 2 ^ c →
      ((k + xs.length : ℕ) : ℝ) * 2 ^ c ≤ φ.maxFinite →
      ∃ r, xs.foldlM φ.fadd s = some r := by
  intro xs
  induction xs with
  | nil => intro k s _ _ _; exact ⟨s, rfl⟩
  | cons x xs ih =>
    intro k s hx hs hn
    have hxc := hx x (by simp)
    have hy : |s + x| ≤ (min k (2 ^ φ.p) : ℕ) * 2 ^ c + 2 ^ c :=
      (abs_add_le s x).trans (by linarith)
    have hstep := seq_step hc hy
    have hc0 := two_zpow_pos c
    have hmin : ((min (k + 1) (2 ^ φ.p) : ℕ) : ℝ) * 2 ^ c ≤ ((k + 1 + xs.length : ℕ) : ℝ) * 2 ^ c := by
      gcongr; omega
    have hfin : |φ.rne (s + x)| ≤ φ.maxFinite := by
      refine hstep.trans (hmin.trans (le_of_eq_of_le ?_ hn))
      simp only [List.length_cons]; push_cast; ring
    have hadd : φ.fadd s x = some (φ.rne (s + x)) := by simp [fadd, hfin]
    rw [List.foldlM_cons, hadd]
    exact ih (k + 1) _ (fun y hy => hx y (by simp [hy])) hstep
      (le_of_eq_of_le (by simp only [List.length_cons]; push_cast; ring) hn)

/-- The sequential sum of at most `n` values bounded by `2 ^ c` does not overflow when
`n * 2 ^ c` is at most the largest finite value. -/
theorem seqSum_ne_none_of_mul {c : ℤ} (hc : φ.qmin ≤ c) {n : ℕ}
    (hn : (n : ℝ) * 2 ^ c ≤ φ.maxFinite) {xs : List ℝ} (hlen : xs.length ≤ n)
    (hx : ∀ x ∈ xs, |x| ≤ 2 ^ c) : φ.seqSum xs ≠ none := by
  obtain ⟨r, hr⟩ := foldlM_seq_bound hc xs 0 0 hx (by simp)
    (le_trans (by gcongr; simpa using hlen) hn)
  simp [seqSum, hr]

/-- Rounding a value within half an ulp of the largest finite value does not overflow. -/
theorem abs_rne_le_maxFinite {y : ℝ} (hy : |y| < φ.maxFinite + 2 ^ φ.qtop / 2) :
    |φ.rne y| ≤ φ.maxFinite := by
  rcases le_or_gt |y| φ.maxFinite with h | h
  · exact abs_rne_le isRep_maxFinite h
  obtain ⟨p', hp'⟩ : ∃ p', φ.p = p' + 1 := ⟨φ.p - 1, by have := φ.hp; omega⟩
  have ht := two_zpow_pos φ.qtop
  have h4 := two_pow_p_ge (φ := φ)
  -- `2 ^ emax = 2 ^ (p - 1) * 2 ^ qtop` and `2 ^ (emax + 1) = 2 ^ p * 2 ^ qtop`
  have he : (2 : ℝ) ^ φ.emax = 2 ^ p' * 2 ^ φ.qtop := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; unfold qtop; omega
  have he1 : (2 : ℝ) ^ (φ.emax + 1) = 2 ^ φ.p * 2 ^ φ.qtop := by
    rw [zpow_add_one₀ (by norm_num), he, hp', pow_succ]; ring
  have hmax := maxFinite_eq (φ := φ)
  rw [hp', pow_succ] at hmax h4
  have hf : φ.fexp y = φ.qtop := by
    rw [fexp_of_bounds (e := φ.emax)]
    · unfold qtop; ring
    · rw [he]; nlinarith
    · rw [he1, hp', pow_succ]; nlinarith
    · have := qmin_le_qtop (φ := φ); unfold qtop at *; omega
  unfold rne
  rw [hf, abs_mul, abs_of_pos ht, hmax]
  gcongr
  -- the rounded significand is below `2 ^ p`, so at most `2 ^ p - 1`
  have hr := roundEven_half (y / 2 ^ φ.qtop)
  have hyq : |y / 2 ^ φ.qtop| < 2 ^ p' * 2 - 1 + 1 / 2 := by
    rw [abs_div, abs_of_pos ht, div_lt_iff₀ ht]; nlinarith
  have : |((roundEven (y / 2 ^ φ.qtop) : ℤ) : ℝ)| < ((2 ^ p' * 2 : ℤ) : ℝ) := by
    push_cast
    calc |((roundEven (y / 2 ^ φ.qtop) : ℤ) : ℝ)|
        = |y / 2 ^ φ.qtop - (y / 2 ^ φ.qtop - roundEven (y / 2 ^ φ.qtop))| := by ring_nf
      _ ≤ |y / 2 ^ φ.qtop| + |y / 2 ^ φ.qtop - roundEven (y / 2 ^ φ.qtop)| := abs_sub _ _
      _ < 2 ^ p' * 2 := by linarith
  have : |roundEven (y / 2 ^ φ.qtop)| ≤ 2 ^ p' * 2 - 1 := by
    have : |roundEven (y / 2 ^ φ.qtop)| < 2 ^ p' * 2 := by exact_mod_cast this
    omega
  have : |((roundEven (y / 2 ^ φ.qtop) : ℤ) : ℝ)| ≤ ((2 ^ p' * 2 - 1 : ℤ) : ℝ) := by
    rw [← Int.cast_abs]; exact_mod_cast this
  push_cast at this; exact this

/-- The sequential sum of values below half an ulp of the largest finite value never
overflows, whatever the number of values: an addition that would pass the largest finite value
rounds back to it. -/
theorem seqSum_ne_none_of_small {xs : List ℝ} (hx : ∀ x ∈ xs, |x| < 2 ^ φ.qtop / 2) :
    φ.seqSum xs ≠ none := by
  suffices ∀ (xs : List ℝ) (s : ℝ), (∀ x ∈ xs, |x| < 2 ^ φ.qtop / 2) → |s| ≤ φ.maxFinite →
      ∃ r, xs.foldlM φ.fadd s = some r by
    obtain ⟨r, hr⟩ := this xs 0 hx (by simp [maxFinite_pos.le])
    simp [seqSum, hr]
  intro xs
  induction xs with
  | nil => intro s _ _; exact ⟨s, rfl⟩
  | cons x xs ih =>
    intro s hx hs
    have hxc := hx x (by simp)
    have hfin : |φ.rne (s + x)| ≤ φ.maxFinite :=
      abs_rne_le_maxFinite ((abs_add_le s x).trans_lt (by linarith))
    have hadd : φ.fadd s x = some (φ.rne (s + x)) := by simp [fadd, hfin]
    rw [List.foldlM_cons, hadd]
    exact ih _ (fun y hy => hx y (by simp [hy])) hfin

/-! ### Pairwise summation -/

theorem pwSum_bound {c : ℤ} (hc : φ.qmin ≤ c) :
    ∀ (n : ℕ) (xs : List ℝ), xs.length = n → (∀ x ∈ xs, |x| ≤ 2 ^ c) →
      (φ.ruN n : ℝ) * 2 ^ c ≤ φ.maxFinite →
      ∃ s, φ.pwSum xs = some s ∧ |s| ≤ φ.ruN n * 2 ^ c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro xs hlen hx hn
  have hc0 := two_zpow_pos c
  match xs with
  | [] => exact ⟨0, by simp [pwSum], by simp; positivity⟩
  | [x] =>
    refine ⟨x, by simp [pwSum], (hx x (by simp)).trans ?_⟩
    have : 1 ≤ φ.ruN n := by simp at hlen; subst hlen; exact (ruN_spec 1).1
    have : (1 : ℝ) ≤ φ.ruN n := by exact_mod_cast this
    nlinarith
  | x :: y :: rest =>
    simp only [List.length_cons] at hlen
    set a := (rest.length + 2) / 2 with ha
    have hla : ((x :: y :: rest).take a).length = a := by simp; omega
    have hlb : ((x :: y :: rest).drop a).length = n - a := by simp; omega
    have hmono : ∀ k ≤ n, (φ.ruN k : ℝ) * 2 ^ c ≤ φ.maxFinite := fun k hk =>
      le_trans (by gcongr; exact_mod_cast ruN_mono hk) hn
    obtain ⟨sa, hsa, hba⟩ := ih a (by omega) _ hla
      (fun z hz => hx z (List.mem_of_mem_take hz)) (hmono a (by omega))
    obtain ⟨sb, hsb, hbb⟩ := ih (n - a) (by omega) _ hlb
      (fun z hz => hx z (List.mem_of_mem_drop hz)) (hmono (n - a) (by omega))
    have hsum : φ.ruN a + φ.ruN (n - a) ≤ φ.ruN n := by
      have := ruN_add (φ := φ) (a := a) (b := n - a) (by omega)
      rwa [show a + (n - a) = n by omega] at this
    have hy : |sa + sb| ≤ φ.ruN n * 2 ^ c := by
      calc |sa + sb| ≤ |sa| + |sb| := abs_add_le _ _
        _ ≤ (φ.ruN a + φ.ruN (n - a) : ℕ) * 2 ^ c := by push_cast; linarith
        _ ≤ φ.ruN n * 2 ^ c := by gcongr
    have hr := abs_rne_le (isRep_of_isRepN (ruN_spec n).2 hc) hy
    have hadd : φ.fadd sa sb = some (φ.rne (sa + sb)) := by simp [fadd, hr.trans hn]
    refine ⟨φ.rne (sa + sb), ?_, hr⟩
    rw [pwSum, ← ha, hsa, hsb]
    simpa using hadd

/-- The pairwise sum of at most `n` values bounded by `2 ^ c` does not overflow when
`n * 2 ^ c` is at most the largest finite value. -/
theorem pwSum_ne_none_of_mul {c : ℤ} (hc : φ.qmin ≤ c) {n : ℕ}
    (hn : (n : ℝ) * 2 ^ c ≤ φ.maxFinite) {xs : List ℝ} (hlen : xs.length ≤ n)
    (hx : ∀ x ∈ xs, |x| ≤ 2 ^ c) : φ.pwSum xs ≠ none := by
  have hc0 := two_zpow_pos c
  obtain ⟨s, hs, _⟩ := pwSum_bound hc xs.length xs rfl hx
    (le_trans (by gcongr; exact_mod_cast ruN_mono hlen) (ruN_mul_le hn))
  simp [hs]

end Fmt

end OpenDP.Float
