/-
IEEE 754 binary floating-point formats and round-to-nearest, ties-to-even.

A format has precision `p` (significand bits, including the implicit bit) and largest exponent
`emax`; `f64` is `p = 53, emax = 1023` and `f32` is `p = 24, emax = 127`. The smallest exponent
is `emin = 1 - emax`, so subnormals are multiples of `2 ^ qmin` with `qmin = emin - p + 1`.

`rne` rounds to the format *with unbounded exponent range*, following the standard
(IEEE 754-2019 §4.3, §7.4): an operation overflows exactly when this rounded result exceeds the
largest finite value `maxFinite` in magnitude, and then returns an infinity. This is the FLT
format with `ZnearestE` rounding of Flocq [Boldo, Melquiond 2011].
-/
import Mathlib

namespace OpenDP.Float

/-- An IEEE 754 binary floating-point format. -/
structure Fmt where
  /-- Precision: the number of significand bits, including the implicit bit. -/
  p : ℕ
  /-- The largest exponent (the exponent bias). -/
  emax : ℤ
  hp : 2 ≤ p
  hemax : 1 ≤ emax

/-- Round to the nearest integer, ties to even. -/
noncomputable def roundEven (y : ℝ) : ℤ :=
  if y - ⌊y⌋ < 1 / 2 then ⌊y⌋
  else if 1 / 2 < y - ⌊y⌋ then ⌊y⌋ + 1
  else if Even ⌊y⌋ then ⌊y⌋ else ⌊y⌋ + 1

theorem roundEven_char (y : ℝ) :
    |y - roundEven y| < 1 / 2 ∨ (|y - roundEven y| = 1 / 2 ∧ Even (roundEven y)) := by
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one y
  unfold roundEven
  split_ifs with ha hb hc
  · left; rw [abs_lt]; constructor <;> linarith
  · left; push_cast; rw [abs_lt]; constructor <;> linarith
  · right; refine ⟨?_, hc⟩; rw [abs_of_nonneg (by linarith)]; push Not at ha hb; linarith
  · right; refine ⟨?_, ?_⟩
    · push_cast; rw [abs_of_nonpos (by push Not at ha; linarith)]; push Not at ha hb; linarith
    · exact (Int.not_even_iff_odd.mp hc).add_one

theorem roundEven_half (y : ℝ) : |y - roundEven y| ≤ 1 / 2 := by
  rcases roundEven_char y with h | h
  · exact h.le
  · exact h.1.le

/-- Two integers within `1 / 2` of the same real are equal, unless both are at distance exactly
`1 / 2`. -/
private theorem int_eq_of_close {y : ℝ} {r s : ℤ} (hr : |y - r| ≤ 1 / 2) (hs : |y - s| ≤ 1 / 2)
    (h : |y - r| < 1 / 2 ∨ |y - s| < 1 / 2) : r = s := by
  have hrs : |(r : ℝ) - s| < 1 := by
    calc |(r : ℝ) - s| = |(y - s) - (y - r)| := by ring_nf
      _ ≤ |y - s| + |y - r| := abs_sub _ _
      _ < 1 := by rcases h with h | h <;> linarith
  have : |r - s| < 1 := by exact_mod_cast hrs
  rw [abs_lt] at this
  omega

/-- `roundEven y` is the nearest integer to `y`. -/
theorem roundEven_nearest (y : ℝ) (z : ℤ) : |y - roundEven y| ≤ |y - z| := by
  by_contra hlt
  push Not at hlt
  have hz : |y - z| ≤ 1 / 2 := le_trans hlt.le (roundEven_half y)
  have := int_eq_of_close hz (roundEven_half y) (Or.inl (lt_of_lt_of_le hlt (roundEven_half y)))
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-- `roundEven` is characterized by `roundEven_char`. -/
theorem roundEven_eq {y : ℝ} {r : ℤ}
    (h : |y - r| < 1 / 2 ∨ (|y - r| = 1 / 2 ∧ Even r)) : roundEven y = r := by
  have hr : |y - r| ≤ 1 / 2 := by rcases h with h | h <;> [exact h.le; exact h.1.le]
  rcases h with h | ⟨h, hev⟩
  · exact int_eq_of_close (roundEven_half y) hr (Or.inr h)
  · rcases roundEven_char y with h' | ⟨h', hev'⟩
    · exact int_eq_of_close (roundEven_half y) hr (Or.inl h')
    · -- both at distance exactly 1/2: they differ by 0 or 1, and are both even
      have hrs : |((roundEven y - r : ℤ) : ℝ)| ≤ 1 := by
        push_cast
        calc |(roundEven y : ℝ) - r| = |(y - r) - (y - roundEven y)| := by ring_nf
          _ ≤ |y - r| + |y - roundEven y| := abs_sub _ _
          _ = 1 := by rw [h, h']; norm_num
      have : |roundEven y - r| ≤ 1 := by exact_mod_cast hrs
      rw [abs_le] at this
      obtain ⟨a, ha⟩ := hev
      obtain ⟨b, hb⟩ := hev'
      omega

theorem roundEven_intCast (z : ℤ) : roundEven z = z :=
  roundEven_eq (Or.inl (by simp))

theorem roundEven_neg (y : ℝ) : roundEven (-y) = -roundEven y := by
  apply roundEven_eq
  have e : |-y - ((-roundEven y : ℤ) : ℝ)| = |y - roundEven y| := by
    push_cast; rw [← abs_neg]; ring_nf
  rw [e, even_neg]
  exact roundEven_char y

namespace Fmt

variable (φ : Fmt)

/-- The exponent of the least significant bit of subnormals: `emin - p + 1`. -/
def qmin : ℤ := 2 - φ.emax - φ.p

/-- The exponent of the least significant bit of the largest binade: `ulp(maxFinite) = 2 ^ qtop`. -/
def qtop : ℤ := φ.emax - φ.p + 1

/-- The largest finite value. -/
noncomputable def maxFinite : ℝ := (2 ^ φ.p - 1) * 2 ^ φ.qtop

/-- Values of the format with unbounded exponent range. Allowing `|m| = 2 ^ p` does not add
values (`2 ^ p * 2 ^ e = 2 ^ (p - 1) * 2 ^ (e + 1)`), but simplifies proofs. -/
def IsRep (x : ℝ) : Prop :=
  ∃ m e : ℤ, |m| ≤ 2 ^ φ.p ∧ φ.qmin ≤ e ∧ x = m * (2 : ℝ) ^ e

/-- The exponent of the least significant bit of a value of the binade of `x`. -/
noncomputable def fexp (x : ℝ) : ℤ := max (Int.log 2 |x| - φ.p + 1) φ.qmin

/-- Round to the nearest value of the format (with unbounded exponent range), ties to even. -/
noncomputable def rne (x : ℝ) : ℝ := roundEven (x / 2 ^ φ.fexp x) * (2 : ℝ) ^ φ.fexp x

variable {φ}

theorem two_zpow_pos (e : ℤ) : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) e

theorem qmin_le_qtop : φ.qmin ≤ φ.qtop := by
  have := φ.hemax; unfold qmin qtop; omega

theorem qmin_nonpos : φ.qmin ≤ 0 := by
  have := φ.hemax; have := φ.hp; unfold qmin; omega

theorem maxFinite_eq : φ.maxFinite = (2 ^ φ.p - 1) * (2 : ℝ) ^ φ.qtop := rfl

theorem two_pow_p_ge : (4 : ℝ) ≤ 2 ^ φ.p := by
  have : (2 : ℝ) ^ 2 ≤ 2 ^ φ.p := pow_le_pow_right₀ (by norm_num) φ.hp
  linarith [show (2 : ℝ) ^ 2 = 4 by norm_num]

theorem maxFinite_pos : 0 < φ.maxFinite := by
  unfold maxFinite
  have := two_pow_p_ge (φ := φ)
  exact mul_pos (by linarith) (two_zpow_pos _)

theorem isRep_neg {x : ℝ} (h : φ.IsRep x) : φ.IsRep (-x) := by
  obtain ⟨m, e, hm, he, rfl⟩ := h
  exact ⟨-m, e, by rwa [abs_neg], he, by push_cast; ring⟩

theorem isRep_zero : φ.IsRep 0 := ⟨0, φ.qmin, by simp, le_rfl, by simp⟩

/-- `k * 2 ^ e` is in the format when `|k| ≤ 2 ^ p`. -/
theorem isRep_of_mul {k : ℤ} {e : ℤ} (hk : |k| ≤ 2 ^ φ.p) (he : φ.qmin ≤ e) :
    φ.IsRep (k * (2 : ℝ) ^ e) := ⟨k, e, hk, he, rfl⟩

theorem isRep_maxFinite : φ.IsRep φ.maxFinite := by
  refine ⟨2 ^ φ.p - 1, φ.qtop, ?_, qmin_le_qtop, by unfold maxFinite; push_cast; ring⟩
  have : (1 : ℤ) ≤ 2 ^ φ.p := one_le_pow₀ (by norm_num)
  rw [abs_of_nonneg (by linarith)]; linarith

/-- `rne x` is a multiple of `2 ^ fexp x` nearest to `x`. -/
theorem rne_nearest_mul (x : ℝ) (z : ℤ) : |x - φ.rne x| ≤ |x - z * (2 : ℝ) ^ φ.fexp x| := by
  have hq := two_zpow_pos (φ.fexp x)
  have key : ∀ w : ℝ, x - w * 2 ^ φ.fexp x = (x / 2 ^ φ.fexp x - w) * 2 ^ φ.fexp x := by
    intro w; field_simp
  unfold rne
  rw [key, key, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (roundEven_nearest _ z) (abs_nonneg _)

theorem rne_isRep (x : ℝ) : φ.IsRep (φ.rne x) := by
  refine ⟨roundEven (x / 2 ^ φ.fexp x), φ.fexp x, ?_, le_max_right _ _, rfl⟩
  have hq := two_zpow_pos (φ.fexp x)
  -- |x / 2 ^ fexp x| ≤ 2 ^ p
  have hy : |x / 2 ^ φ.fexp x| ≤ 2 ^ φ.p := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hlt := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) |x|
    push_cast at hlt
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    refine le_trans hlt.le (zpow_le_zpow_right₀ (by norm_num) ?_)
    have := le_max_left (Int.log 2 |x| - φ.p + 1) φ.qmin
    unfold fexp; omega
  have h := roundEven_half (x / 2 ^ φ.fexp x)
  have : |((roundEven (x / 2 ^ φ.fexp x) : ℤ) : ℝ)| < 2 ^ φ.p + 1 := by
    calc |((roundEven (x / 2 ^ φ.fexp x) : ℤ) : ℝ)|
        = |x / 2 ^ φ.fexp x - (x / 2 ^ φ.fexp x - roundEven (x / 2 ^ φ.fexp x))| := by ring_nf
      _ ≤ |x / 2 ^ φ.fexp x| + |x / 2 ^ φ.fexp x - roundEven (x / 2 ^ φ.fexp x)| := abs_sub _ _
      _ < 2 ^ φ.p + 1 := by linarith
  have : |roundEven (x / 2 ^ φ.fexp x)| < 2 ^ φ.p + 1 := by exact_mod_cast this
  omega

theorem rne_zero : φ.rne 0 = 0 := by
  have : roundEven 0 = 0 := by exact_mod_cast roundEven_intCast 0
  simp [rne, this]

/-- `rne x` is a value of the format nearest to `x`. -/
theorem rne_nearest (x : ℝ) {f : ℝ} (hf : φ.IsRep f) : |x - φ.rne x| ≤ |x - f| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [rne_zero]
  obtain ⟨m, r, hm, hr, rfl⟩ := hf
  set q := φ.fexp x with hqdef
  rcases le_or_gt q r with h | h
  · -- `f` is a multiple of `2 ^ q`
    have e : (m : ℝ) * 2 ^ r = ((m * 2 ^ (r - q).toNat : ℤ) : ℝ) * 2 ^ q := by
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 2; omega
    rw [e]; exact rne_nearest_mul x _
  · -- `f` is in a lower binade, so `|f| ≤ 2 ^ L ≤ |x|` where `L = log₂ |x|`,
    -- and `±2 ^ L` is a multiple of `2 ^ q` at least as close to `x` as `f`
    set L := Int.log 2 |x| with hL
    have hqL : q = L - φ.p + 1 := by
      have : q = max (L - φ.p + 1) φ.qmin := rfl
      omega
    have hax : 0 < |x| := abs_pos.mpr hx
    have hLx : (2 : ℝ) ^ L ≤ |x| := by
      have := Int.zpow_log_le_self (b := 2) (by norm_num) hax; exact_mod_cast this
    have hf : |(m : ℝ) * 2 ^ r| ≤ 2 ^ L := by
      rw [abs_mul, abs_of_pos (two_zpow_pos r)]
      have hm' : |(m : ℝ)| ≤ 2 ^ φ.p := by exact_mod_cast hm
      calc |(m : ℝ)| * 2 ^ r ≤ 2 ^ φ.p * 2 ^ r :=
            mul_le_mul_of_nonneg_right hm' (two_zpow_pos r).le
        _ = 2 ^ ((φ.p : ℤ) + r) := by rw [zpow_add₀ (by norm_num), zpow_natCast]
        _ ≤ 2 ^ L := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hp1 : 1 ≤ φ.p := by have := φ.hp; omega
    have hg : ∀ s : ℤ, s = 1 ∨ s = -1 →
        ((s * 2 ^ (φ.p - 1) : ℤ) : ℝ) * 2 ^ q = s * 2 ^ L := by
      intro s _
      push_cast
      rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 2; push_cast [Nat.cast_sub hp1]; omega
    have hclose : |x - φ.rne x| ≤ |x| - 2 ^ L := by
      rcases le_or_gt 0 x with hx0 | hx0
      · have := rne_nearest_mul (φ := φ) x (1 * 2 ^ (φ.p - 1))
        rw [hg 1 (Or.inl rfl)] at this
        have hx' : |x| = x := abs_of_nonneg hx0
        have e : |x - ((1 : ℤ) : ℝ) * 2 ^ L| = |x| - 2 ^ L := by
          rw [hx']; push_cast; rw [one_mul, abs_of_nonneg (by linarith)]
        linarith
      · have := rne_nearest_mul (φ := φ) x (-1 * 2 ^ (φ.p - 1))
        rw [hg (-1) (Or.inr rfl)] at this
        have hx' : |x| = -x := abs_of_neg hx0
        have e : |x - ((-1 : ℤ) : ℝ) * 2 ^ L| = |x| - 2 ^ L := by
          rw [hx']; push_cast; rw [abs_of_nonpos (by linarith)]; ring
        linarith
    calc |x - φ.rne x| ≤ |x| - 2 ^ L := hclose
      _ ≤ |x| - |(m : ℝ) * 2 ^ r| := by linarith
      _ ≤ |x - (m : ℝ) * 2 ^ r| := abs_sub_abs_le_abs_sub _ _

theorem rne_of_isRep {f : ℝ} (hf : φ.IsRep f) : φ.rne f = f := by
  have := rne_nearest f hf
  simp only [sub_self, abs_zero] at this
  have := abs_nonneg (f - φ.rne f)
  have : f - φ.rne f = 0 := abs_eq_zero.mp (by linarith)
  linarith

/-- Rounding to nearest is monotone. -/
theorem rne_mono {x y : ℝ} (h : x ≤ y) : φ.rne x ≤ φ.rne y := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  by_contra hlt
  push Not at hlt
  have h1 := rne_nearest x (rne_isRep (φ := φ) y)
  have h2 := rne_nearest y (rne_isRep (φ := φ) x)
  rcases abs_cases (x - φ.rne x) with ⟨a1, _⟩ | ⟨a1, _⟩ <;>
  rcases abs_cases (x - φ.rne y) with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
  rcases abs_cases (y - φ.rne y) with ⟨a3, _⟩ | ⟨a3, _⟩ <;>
  rcases abs_cases (y - φ.rne x) with ⟨a4, _⟩ | ⟨a4, _⟩ <;>
  linarith

theorem rne_le_of_le {B y : ℝ} (hB : φ.IsRep B) (h : y ≤ B) : φ.rne y ≤ B :=
  rne_of_isRep hB ▸ rne_mono h

theorem le_rne_of_le {B y : ℝ} (hB : φ.IsRep B) (h : B ≤ y) : B ≤ φ.rne y :=
  rne_of_isRep hB ▸ rne_mono h

/-- Rounding cannot leave an interval `[-B, B]` whose end points are in the format. -/
theorem abs_rne_le {B y : ℝ} (hB : φ.IsRep B) (h : |y| ≤ B) : |φ.rne y| ≤ B := by
  rw [abs_le] at h ⊢
  have := le_rne_of_le (isRep_neg hB) h.1
  exact ⟨this, rne_le_of_le hB h.2⟩

theorem rne_neg (x : ℝ) : φ.rne (-x) = -φ.rne x := by
  have : φ.fexp (-x) = φ.fexp x := by simp [fexp]
  simp only [rne, this, neg_div, roundEven_neg]
  push_cast; ring

/-- The exponent function in the binade `[2 ^ e, 2 ^ (e + 1))`. -/
theorem fexp_of_bounds {x : ℝ} {e : ℤ} (h1 : (2 : ℝ) ^ e ≤ |x|) (h2 : |x| < 2 ^ (e + 1))
    (he : φ.qmin ≤ e - φ.p + 1) : φ.fexp x = e - φ.p + 1 := by
  have hax : 0 < |x| := lt_of_lt_of_le (two_zpow_pos e) h1
  have hlog : Int.log 2 |x| = e := by
    have a := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hax).mp (by exact_mod_cast h1)
    have b := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hax).mp (by exact_mod_cast h2)
    omega
  unfold fexp; rw [hlog]; omega

end Fmt

end OpenDP.Float
