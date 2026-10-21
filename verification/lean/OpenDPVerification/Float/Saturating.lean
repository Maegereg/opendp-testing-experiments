/-
The rounding error of OpenDP's sequential saturating float sum.

`Sequential::<T>::saturating_sum` folds `sum.saturating_add(v)`, that is
`(sum + v).clamp(T::MIN, T::MAX)`, from zero. An IEEE addition that overflows returns an
infinity, which the clamp maps back to `±MAX`, so each step is `clampF (rne (s + x))`.

Its ideal counterpart is the exact sum clamped at every step, `clampSeqSum`. Clamping is
1-Lipschitz, so the two drift apart by at most the rounding error of each addition,
`2 ^ -p * |s + x|` (`rne_add_err`). The float partial sums stay below `k * M` after `k` steps,
for `M = 2 ^ c` the power of two above the bound on the values (`seq_step`), so with `M <= 2 m`
the total drift is at most `2 ^ -p * n ^ 2 * m` (`satSeqSum_err`).
-/
import OpenDPVerification.Float.Sum

namespace OpenDP.Float

namespace Fmt

variable (φ : Fmt)

/-- Clamping to the finite range: `x.clamp(T::MIN, T::MAX)`. -/
noncomputable def clampF (x : ℝ) : ℝ := max (-φ.maxFinite) (min φ.maxFinite x)

/-- Saturating addition, `a.saturating_add(b)` for floats: IEEE addition, then clamping
(an infinity clamps to `±MAX`, which is the clamped rounded value). -/
noncomputable def satAdd (a b : ℝ) : ℝ := φ.clampF (φ.rne (a + b))

/-- `Sequential::<T>::saturating_sum`: `arg.iter().fold(T::zero(), |sum, v| sum.saturating_add(v))`. -/
noncomputable def satSeqSum (xs : List ℝ) : ℝ := xs.foldl φ.satAdd 0

/-- The exact sum, clamped to the finite range after every addition. -/
noncomputable def clampSeqSum (xs : List ℝ) : ℝ := xs.foldl (fun s x => φ.clampF (s + x)) 0

variable {φ}

theorem clampF_sub_le {a b : ℝ} (h : a ≤ b) :
    φ.clampF a ≤ φ.clampF b ∧ φ.clampF b - φ.clampF a ≤ b - a := by
  have := maxFinite_pos (φ := φ)
  simp only [clampF, max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Clamping is 1-Lipschitz. -/
theorem clampF_lipschitz (x y : ℝ) : |φ.clampF x - φ.clampF y| ≤ |x - y| := by
  rcases le_total x y with h | h
  · have := clampF_sub_le (φ := φ) h
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this.2
  · have := clampF_sub_le (φ := φ) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact this.2

theorem abs_clampF_le (x : ℝ) : |φ.clampF x| ≤ |x| := by
  have := clampF_lipschitz (φ := φ) x 0
  have h0 : φ.clampF 0 = 0 := by
    have := maxFinite_pos (φ := φ)
    simp only [clampF]; rw [min_eq_right this.le, max_eq_right (by linarith)]
  rwa [h0, sub_zero, sub_zero] at this

theorem clampF_isRep {x : ℝ} (hx : φ.IsRep x) : φ.IsRep (φ.clampF x) := by
  simp only [clampF, max_def, min_def]
  split_ifs <;> first | exact hx | exact isRep_maxFinite | exact isRep_neg isRep_maxFinite

/-- Values of the format are integer multiples of `2 ^ qmin`. -/
theorem isRep_mul_qmin {x : ℝ} (hx : φ.IsRep x) : ∃ k : ℤ, x = k * (2 : ℝ) ^ φ.qmin := by
  obtain ⟨m, e, _, he, rfl⟩ := hx
  refine ⟨m * 2 ^ (e - φ.qmin).toNat, ?_⟩
  have : (2 : ℝ) ^ e = 2 ^ ((e - φ.qmin).toNat : ℤ) * 2 ^ φ.qmin := by
    rw [← zpow_add₀ (by norm_num)]; congr 1; omega
  rw [this, zpow_natCast]; push_cast; ring

/-- The rounding error of adding two values of the format is at most `2 ^ -p` times the sum:
results below the normal range are exact. -/
theorem rne_add_err {a b : ℝ} (ha : φ.IsRep a) (hb : φ.IsRep b) :
    |φ.rne (a + b) - (a + b)| ≤ 2 ^ (-(φ.p : ℤ)) * |a + b| := by
  set z := a + b with hz
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, rne_zero]; simp
  have hq := two_zpow_pos (φ.fexp z)
  -- the error is at most half a unit in the last place
  have herr : |φ.rne z - z| ≤ 2 ^ φ.fexp z / 2 := by
    have key : φ.rne z - z = -((z / 2 ^ φ.fexp z - roundEven (z / 2 ^ φ.fexp z)) * 2 ^ φ.fexp z) := by
      unfold rne; field_simp; ring
    rw [key, abs_neg, abs_mul, abs_of_pos hq]
    have := roundEven_half (z / 2 ^ φ.fexp z)
    nlinarith
  by_cases hn : φ.qmin ≤ Int.log 2 |z| - φ.p + 1
  · -- normal range: half an ulp is at most `2 ^ -p * |z|`
    have hf : φ.fexp z = Int.log 2 |z| - φ.p + 1 := max_eq_left hn
    have hlog : (2 : ℝ) ^ Int.log 2 |z| ≤ |z| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr h0)
    have : (2 : ℝ) ^ φ.fexp z / 2 = 2 ^ Int.log 2 |z| * 2 ^ (-(φ.p : ℤ)) := by
      rw [hf, ← zpow_add₀ (by norm_num), div_eq_iff (by norm_num), ← zpow_add_one₀ (by norm_num)]
      ring_nf
    rw [this] at herr
    have hp := two_zpow_pos (-(φ.p : ℤ))
    nlinarith
  · -- below the normal range, `z` is a multiple of `2 ^ qmin = 2 ^ fexp z`, so it is exact
    have hf : φ.fexp z = φ.qmin := max_eq_right (by omega)
    obtain ⟨ka, hka⟩ := isRep_mul_qmin ha
    obtain ⟨kb, hkb⟩ := isRep_mul_qmin hb
    have hzk : z / 2 ^ φ.fexp z = ((ka + kb : ℤ) : ℝ) := by
      rw [hf, hz, hka, hkb]; push_cast; field_simp
    have : φ.rne z = z := by
      unfold rne; rw [hzk, roundEven_intCast, ← hzk]; field_simp
    rw [this, sub_self, abs_zero]
    positivity

/-- A value of the format below `2 ^ qmin` in magnitude is zero. -/
theorem isRep_eq_zero {x : ℝ} (hx : φ.IsRep x) (h : |x| < 2 ^ φ.qmin) : x = 0 := by
  obtain ⟨k, rfl⟩ := isRep_mul_qmin hx
  have hq := two_zpow_pos φ.qmin
  rw [abs_mul, abs_of_pos hq] at h
  have : |(k : ℝ)| < 1 := by nlinarith
  have : |k| < 1 := by exact_mod_cast this
  have : k = 0 := by rw [abs_lt] at this; omega
  simp [this]

/-- The drift between the saturating float sum and the clamped exact sum, from accumulators
`s` (float, after `k` additions of values bounded by `2 ^ c`) and `t`. -/
theorem satSeq_err_aux {c : ℤ} (hc : φ.qmin ≤ c) {m : ℝ} :
    ∀ (xs : List ℝ) (k : ℕ) (s t : ℝ),
      (∀ x ∈ xs, φ.IsRep x ∧ |x| ≤ m ∧ |x| ≤ 2 ^ c) → φ.IsRep s →
      |s| ≤ (min k (2 ^ φ.p) : ℕ) * 2 ^ c →
      |xs.foldl φ.satAdd s - xs.foldl (fun s x => φ.clampF (s + x)) t| ≤
        |s - t| + 2 ^ (-(φ.p : ℤ)) *
          (((xs.length : ℝ) * k + (xs.length : ℝ) * ((xs.length : ℝ) - 1) / 2) * 2 ^ c
            + xs.length * m) := by
  intro xs
  induction xs with
  | nil => intro k s t _ _ _; simp
  | cons x xs ih =>
    intro k s t hx hs hsk
    obtain ⟨hxr, hxm, hxc⟩ := hx x (by simp)
    have hu := two_zpow_pos (-(φ.p : ℤ))
    have hc0 := two_zpow_pos c
    -- the float partial sum stays below `min(k + 1, 2 ^ p) * 2 ^ c`
    have hy : |s + x| ≤ (min k (2 ^ φ.p) : ℕ) * 2 ^ c + 2 ^ c :=
      (abs_add_le s x).trans (by linarith)
    have hstep : |φ.satAdd s x| ≤ (min (k + 1) (2 ^ φ.p) : ℕ) * 2 ^ c :=
      (abs_clampF_le _).trans (seq_step hc hy)
    -- one step adds at most `2 ^ -p * (k * 2 ^ c + m)` to the drift
    have hmk : ((min k (2 ^ φ.p) : ℕ) : ℝ) ≤ k := by exact_mod_cast min_le_left _ _
    have hsx : |s + x| ≤ k * 2 ^ c + m := by
      calc |s + x| ≤ |s| + |x| := abs_add_le s x
        _ ≤ (min k (2 ^ φ.p) : ℕ) * 2 ^ c + m := by linarith
        _ ≤ k * 2 ^ c + m := by gcongr
    have hd : |φ.satAdd s x - φ.clampF (t + x)| ≤ |s - t| + 2 ^ (-(φ.p : ℤ)) * (k * 2 ^ c + m) := by
      calc |φ.satAdd s x - φ.clampF (t + x)| ≤ |φ.rne (s + x) - (t + x)| := clampF_lipschitz _ _
        _ = |(φ.rne (s + x) - (s + x)) + (s - t)| := by ring_nf
        _ ≤ |φ.rne (s + x) - (s + x)| + |s - t| := abs_add_le _ _
        _ ≤ 2 ^ (-(φ.p : ℤ)) * |s + x| + |s - t| := by linarith [rne_add_err hs hxr]
        _ ≤ |s - t| + 2 ^ (-(φ.p : ℤ)) * (k * 2 ^ c + m) := by nlinarith
    have hrec := ih (k + 1) (φ.satAdd s x) (φ.clampF (t + x)) (fun y hy => hx y (by simp [hy]))
      (clampF_isRep (rne_isRep _)) hstep
    simp only [List.foldl_cons, List.length_cons]
    refine hrec.trans ?_
    push_cast
    have : (2 : ℝ) ^ (-(φ.p : ℤ)) * ((↑xs.length * (↑k + 1) + ↑xs.length * (↑xs.length - 1) / 2) * 2 ^ c
        + ↑xs.length * m) + 2 ^ (-(φ.p : ℤ)) * (k * 2 ^ c + m)
        = 2 ^ (-(φ.p : ℤ)) * (((↑xs.length + 1) * ↑k + (↑xs.length + 1) * (↑xs.length + 1 - 1) / 2) * 2 ^ c
        + (↑xs.length + 1) * m) := by ring
    linarith

/-- The sequential saturating float sum of values of the format bounded by `m` is within
`2 ^ -p * n ^ 2 * m` of the clamped exact sum. -/
theorem satSeqSum_err {m : ℝ} {xs : List ℝ} (hx : ∀ x ∈ xs, φ.IsRep x ∧ |x| ≤ m) :
    |φ.satSeqSum xs - φ.clampSeqSum xs| ≤ 2 ^ (-(φ.p : ℤ)) * (xs.length : ℝ) ^ 2 * m := by
  have hu := two_zpow_pos (-(φ.p : ℤ))
  rcases xs with _ | ⟨x0, xs'⟩
  · simp [satSeqSum, clampSeqSum]
  set xs := x0 :: xs' with hxs
  have hx0 : x0 ∈ xs := by simp [hxs]
  have hm : 0 ≤ m := (abs_nonneg x0).trans (hx x0 hx0).2
  rcases lt_or_ge m (2 ^ φ.qmin) with hsmall | hbig
  · -- every value is zero, and so are both sums
    have hz : ∀ x ∈ xs, x = 0 := fun x h =>
      isRep_eq_zero (hx x h).1 (lt_of_le_of_lt (hx x h).2 hsmall)
    have h0 : φ.clampF 0 = 0 := by
      have := maxFinite_pos (φ := φ)
      simp only [clampF]; rw [min_eq_right this.le, max_eq_right (by linarith)]
    have hfold : ∀ ys : List ℝ, (∀ y ∈ ys, y = 0) →
        ys.foldl φ.satAdd 0 = 0 ∧ ys.foldl (fun s x => φ.clampF (s + x)) 0 = 0 := by
      intro ys hys
      induction ys with
      | nil => simp
      | cons y ys ih =>
        have hy0 := hys y (by simp)
        simp only [List.foldl_cons, hy0, add_zero, satAdd, rne_zero, h0]
        exact ih (fun z hz => hys z (by simp [hz]))
    obtain ⟨h1, h2⟩ := hfold xs hz
    simp only [satSeqSum, clampSeqSum, h1, h2, sub_self, abs_zero]
    positivity
  · -- `M = 2 ^ c` with `m <= M < 2 m`
    set c := Int.clog 2 m
    have hmc : m ≤ 2 ^ c := Int.self_le_zpow_clog (by norm_num) m
    have hm0 : 0 < m := lt_of_lt_of_le (two_zpow_pos _) hbig
    have hcm : (2 : ℝ) ^ (c - 1) < m := Int.zpow_pred_clog_lt_self (by norm_num) hm0
    have hc : φ.qmin ≤ c := by
      by_contra h
      have : (2 : ℝ) ^ c ≤ 2 ^ (φ.qmin - 1) := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have : (2 : ℝ) ^ (φ.qmin - 1) < 2 ^ φ.qmin := zpow_lt_zpow_right₀ (by norm_num) (by omega)
      linarith
    have hM : (2 : ℝ) ^ c ≤ 2 * m := by
      rw [show c = (c - 1) + 1 by ring, zpow_add_one₀ (by norm_num)]; linarith
    have h := satSeq_err_aux hc xs 0 0 0
      (fun x h => ⟨(hx x h).1, (hx x h).2, (hx x h).2.trans hmc⟩) isRep_zero (by simp)
    simp only [sub_zero, abs_zero, zero_add, Nat.cast_zero, mul_zero] at h
    refine h.trans ?_
    have hn : (1 : ℝ) ≤ xs.length := by
      have := List.length_pos_of_mem hx0; exact_mod_cast this
    have : ((xs.length : ℝ) * ((xs.length : ℝ) - 1) / 2) * 2 ^ c ≤
        ((xs.length : ℝ) * ((xs.length : ℝ) - 1) / 2) * (2 * m) := by
      gcongr
    nlinarith
