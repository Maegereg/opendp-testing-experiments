/-
`make_np_clamp` (`python/src/opendp/extras/numpy/_make_np_clamp/__init__.py`).

The transformation clamps each row of a 2-dimensional numpy array to an L`p` ball (`p ∈ {1, 2}`)
of radius `norm` around `origin`, and claims:
* the output is a member of `array2_domain(norm=norm, p=p, origin=origin, nan=False, ...)`: no NaN,
  and every row satisfies the domain's check `np.linalg.norm(x - origin, ord=p, axis=1) ≤ norm`;
* the stability map `d_in ↦ d_in` under the symmetric distance.

## The model

`_function` is transcribed by hand below (`clamp`), against a model of the numpy operations it
uses. `clampV0` transcribes the code before the fixes (F9-F17), and the counterexamples are about
it. The model is trusted:
* Element-wise operations (`-`, `+`, `*`, `/`, `np.sqrt`, `np.abs`, `np.maximum`,
  `np.nan_to_num`) on `float64` (or `float32`) arrays are IEEE 754 operations, rounding to
  nearest, ties to even (`Fmt.rne`), on each element (`F64`, with infinities and NaN).
  Signed zeros are not modelled.
* `np.linalg.norm(x, ord=p, axis=1)` is `add.reduce(abs(x), axis=1)` (`p = 1`) or
  `sqrt(add.reduce(x * x, axis=1))` (`p = 2`) (numpy's `linalg/_linalg.py`), and
  `add.reduce` adds the elements of each row along a binary tree that depends only on the row
  length (`Plan`): numpy's pairwise summation is such a tree. This holds for C-ordered arrays,
  which the fixed code ensures (`np.ascontiguousarray`); for Fortran-ordered arrays numpy sums in
  a different order (F15).
* Before the fixes, `current_norm.max()` raised on an empty array (`clampV0`).
* One format: the data, `origin` (cast to the data type) and the bound `norm_T` (the largest value
  of the data type at most `norm`) are in the same format. The domain's check compares with `norm`
  exactly, so passing it with `norm_T ≤ norm` (`memberNorm`) implies passing it with `norm`.

## Results

* Positive, for the fixed code: `clamp_map` (each output row depends only on its input row,
  despite the loop over the whole array), `clamp_stable` (`d_out ≤ d_in`), `clamp_no_nan`,
  `clamp_member` (every output row passes the domain's norm check, for any origin),
  `clamp_empty`, `clamp_terminates` (the loop terminates when `norm` is a normal float, and for
  `p = 1` at least `d` times the smallest normal float; `TermHyp.of_min`, `min_norm_f64`,
  `min_norm_f32`: implied by `make_np_clamp`'s minimum norm), and `clamp_true_norm` (with origin
  zero, the true norms of output rows exceed the bound by at most rounding error).
* Counterexamples for the code before the fixes (`verification/FINDINGS.md`), each a concrete
  input run through the model: `origin_rounding` (F9), `l2_underflow` (F10), `nonterm_subnormal`
  and `nonterm_normal` (F11), `max_bound_overflow` (F12), `empty_error` (F13),
  `cardinalities` (F14).
-/
import OpenDPVerification.Float.Overflow
import OpenDPVerification.Float.Saturating

namespace OpenDP.NpClamp

open OpenDP.Float

/-- A floating-point value: finite, an infinity (`inf true` is `-inf`), or NaN. -/
inductive F64 where
  | fin (x : ℝ)
  | inf (neg : Bool)
  | nan
  deriving Inhabited

namespace F64

variable (φ : Fmt)

/-- IEEE rounding of an exact result: an infinity when it overflows. -/
noncomputable def round (x : ℝ) : F64 :=
  if |φ.rne x| ≤ φ.maxFinite then fin (φ.rne x) else inf (decide (x < 0))

/-- `a + b` -/
noncomputable def add : F64 → F64 → F64
  | fin a, fin b => round φ (a + b)
  | inf s, fin _ => inf s
  | fin _, inf s => inf s
  | inf s, inf t => if s = t then inf s else nan
  | _, _ => nan

/-- `a - o` for a finite `o`. -/
noncomputable def subR (a : F64) (o : ℝ) : F64 :=
  match a with
  | fin a => round φ (a - o)
  | inf s => inf s
  | nan => nan

/-- `a + o` for a finite `o`. -/
noncomputable def addR (a : F64) (o : ℝ) : F64 :=
  match a with
  | fin a => round φ (a + o)
  | inf s => inf s
  | nan => nan

/-- `abs(a)` -/
def abs : F64 → F64
  | fin a => fin |a|
  | inf _ => inf false
  | nan => nan

/-- `a * a` -/
noncomputable def sq : F64 → F64
  | fin a => round φ (a * a)
  | inf _ => inf false
  | nan => nan

/-- `sqrt(a)` -/
noncomputable def sqrt : F64 → F64
  | fin a => if a < 0 then nan else round φ (Real.sqrt a)
  | inf false => inf false
  | inf true => nan
  | nan => nan

/-- `a / b` for finite `a` and `b ≠ 0`. -/
noncomputable def div (a b : ℝ) : F64 := round φ (a / b)

/-- `np.nan_to_num(a)`: NaN to 0, infinities to the largest finite values. -/
noncomputable def nanToNum : F64 → ℝ
  | fin a => a
  | inf false => φ.maxFinite
  | inf true => -φ.maxFinite
  | nan => 0

/-- `a > b` for a finite `b`: false for NaN. -/
def gt : F64 → ℝ → Prop
  | fin a, b => b < a
  | inf neg, _ => neg = false
  | nan, _ => False

/-- The value of a finite float (the operations used on it below never produce others). -/
def toR : F64 → ℝ
  | fin a => a
  | _ => 0

end F64

open F64

/-- A summation tree: `add.reduce` adds the elements at the leaves along the tree. -/
inductive STree where
  | leaf (i : ℕ)
  | node (l r : STree)

namespace STree

def leaves : STree → List ℕ
  | leaf i => [i]
  | node l r => l.leaves ++ r.leaves

noncomputable def eval (φ : Fmt) (xs : List F64) : STree → F64
  | leaf i => xs.getD i (fin 0)
  | node l r => F64.add φ (l.eval φ xs) (r.eval φ xs)

end STree

/-- numpy's summation order: one tree per row length, whose leaves are the row's positions. -/
structure Plan where
  tree : ℕ → STree
  perm : ∀ n, 0 < n → (tree n).leaves.Perm (List.range n)

/-- `add.reduce(xs)` (0 for an empty row). -/
noncomputable def reduce (φ : Fmt) (P : Plan) (xs : List F64) : F64 :=
  if xs = [] then fin 0 else (P.tree xs.length).eval φ xs

/-- The norm order `p`. -/
inductive Ord where
  | l1
  | l2

/-- `np.linalg.norm(row, ord=p)` -/
noncomputable def rowNorm (φ : Fmt) (P : Plan) (o : Ord) (row : List F64) : F64 :=
  match o with
  | .l1 => reduce φ P (row.map F64.abs)
  | .l2 => F64.sqrt φ (reduce φ P (row.map (F64.sq φ)))

/-- The parameters of `make_np_clamp`, and numpy's summation order. -/
structure Clamp (φ : Fmt) where
  P : Plan
  ord : Ord
  /-- `norm` -/
  bound : ℝ
  /-- `origin`, one value per column (`0.0` is a row of zeros). -/
  origin : List ℝ

namespace Clamp

variable {φ : Fmt} (C : Clamp φ)

/-- `nan_to_num(np.linalg.norm(row, ord=p))`, as in `get_norm`. -/
noncomputable def cur (r : List ℝ) : ℝ := nanToNum φ (rowNorm φ C.P C.ord (r.map fin))

/-- The row is above the bound: it makes `current_norm.max() > norm` hold. -/
def above (r : List ℝ) : Prop := C.bound < C.cur r

/-- `np.maximum(np.nan_to_num(current_norm / norm), 1)` for a row. -/
noncomputable def factor (r : List ℝ) : ℝ := max (nanToNum φ (F64.div φ (C.cur r) C.bound)) 1

/-- One pass of the loop on a row: `arg /= factor`. -/
noncomputable def body (r : List ℝ) : List ℝ := r.map fun a => toR (F64.div φ a (C.factor r))

open Classical in
/-- `while current_norm.max() > norm: ...`, with fuel; `none` when the fuel runs out. -/
noncomputable def loop : ℕ → List (List ℝ) → Option (List (List ℝ))
  | 0, rows => if ∃ r ∈ rows, C.above r then none else some rows
  | n + 1, rows => if ∃ r ∈ rows, C.above r then loop n (rows.map C.body) else some rows

/-- `np.nan_to_num(arg - origin)` for a row. -/
noncomputable def pre (row : List F64) : List ℝ :=
  List.zipWith (fun a o => nanToNum φ (F64.subR φ a o)) row C.origin

/-- `arg + origin` for a row. -/
noncomputable def postV0 (r : List ℝ) : List F64 :=
  List.zipWith (fun a o => F64.round φ (a + o)) r C.origin

/-- The domain's norm check rejects a row: `np.linalg.norm(row - origin, ord=p) > norm`. -/
def outside (row : List F64) : Prop :=
  (rowNorm φ C.P C.ord (List.zipWith (F64.subR φ) row C.origin)).gt C.bound

/-- The domain's norm check accepts a row. -/
def memberNorm (row : List F64) : Prop := ¬ C.outside row

open Classical in
/-- `out = arg + origin` for a row, replaced by `origin` when the norm check rejects it:
`out[outside] = origin`. -/
noncomputable def post (r : List ℝ) : List F64 :=
  if C.outside (C.postV0 r) then C.origin.map fin else C.postV0 r

/-- The outcome of `_function`: an output, an exception, or no termination (within the fuel). -/
inductive Res where
  | ok (out : List (List F64))
  | error
  | diverge

/-- `_function(x)` before the fixes, with fuel for the loop: it raised on the empty dataset and
returned `arg + origin` unchecked. The counterexamples F9-F14 are about it. -/
noncomputable def clampV0 (n : ℕ) (x : List (List F64)) : Res :=
  if x = [] then .error
  else match C.loop n (x.map C.pre) with
    | some rows => .ok (rows.map C.postV0)
    | none => .diverge

/-- `_function(x)`, with fuel for the loop. -/
noncomputable def clamp (n : ℕ) (x : List (List F64)) : Res :=
  match C.loop n (x.map C.pre) with
    | some rows => .ok (rows.map C.post)
    | none => .diverge

end Clamp

/-! ## Float lemmas -/

section Lemmas

variable {φ : Fmt}

/-- A finite value of the format. -/
def Ok (φ : Fmt) (a : ℝ) : Prop := φ.IsRep a ∧ |a| ≤ φ.maxFinite

theorem isRep_one : φ.IsRep 1 :=
  ⟨1, 0, by simp; exact one_le_pow₀ (by norm_num), Fmt.qmin_nonpos, by simp⟩

theorem isRep_abs {a : ℝ} (h : φ.IsRep a) : φ.IsRep |a| := by
  rcases abs_cases a with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e]
  · exact h
  · exact Fmt.isRep_neg h

theorem one_le_maxFinite : 1 ≤ φ.maxFinite := by
  have h4 := Fmt.two_pow_p_ge (φ := φ)
  have hp := φ.hp
  have he := φ.hemax
  -- `(2 ^ p - 1) 2 ^ (emax - p + 1) ≥ 2 ^ (p - 1) 2 ^ (emax - p + 1) = 2 ^ emax ≥ 1`
  have h1 : (2 : ℝ) ^ (φ.p - 1) ≤ 2 ^ φ.p - 1 := by
    have : (2 : ℝ) ^ φ.p = 2 * 2 ^ (φ.p - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (1 : ℝ) ≤ 2 ^ (φ.p - 1) := one_le_pow₀ (by norm_num)
    linarith
  have h2 : (2 : ℝ) ^ (φ.p - 1) * 2 ^ φ.qtop = 2 ^ φ.emax := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1
    unfold Fmt.qtop; push_cast [Nat.cast_sub (by omega : 1 ≤ φ.p)]; ring
  have h3 : (1 : ℝ) ≤ 2 ^ φ.emax := one_le_zpow₀ (by norm_num) (by omega)
  unfold Fmt.maxFinite
  nlinarith [Fmt.two_zpow_pos φ.qtop]

theorem ok_zero : Ok φ 0 := ⟨Fmt.isRep_zero, by simp; exact Fmt.maxFinite_pos.le⟩

theorem ok_one : Ok φ 1 := ⟨isRep_one, by simp; exact one_le_maxFinite⟩

theorem ok_max : Ok φ φ.maxFinite := ⟨Fmt.isRep_maxFinite, by rw [abs_of_pos Fmt.maxFinite_pos]⟩

theorem ok_neg_max : Ok φ (-φ.maxFinite) :=
  ⟨Fmt.isRep_neg Fmt.isRep_maxFinite, by rw [abs_neg, abs_of_pos Fmt.maxFinite_pos]⟩

/-- `rne x = r` when every other value of the format is farther from `x`. -/
theorem rne_eq_of_closer {x r : ℝ} (hr : φ.IsRep r)
    (h : ∀ s, φ.IsRep s → s ≠ r → |x - r| < |x - s|) : φ.rne x = r := by
  by_contra hne
  have h1 := h _ (Fmt.rne_isRep x) hne
  have h2 := Fmt.rne_nearest x hr
  linarith

/-- Values below half the smallest subnormal round to zero. -/
theorem rne_tiny {x : ℝ} (h : |x| < 2 ^ φ.qmin / 2) : φ.rne x = 0 := by
  apply rne_eq_of_closer Fmt.isRep_zero
  intro s hs hs0
  have hq : (2 : ℝ) ^ φ.qmin ≤ |s| := by
    by_contra hlt; push Not at hlt; exact hs0 (Fmt.isRep_eq_zero hs hlt)
  have := abs_sub_abs_le_abs_sub s x
  rw [abs_sub_comm s x] at this
  simp only [sub_zero]
  linarith

theorem round_of_ok {a : ℝ} (h : Ok φ a) : F64.round φ a = fin a := by
  simp [F64.round, Fmt.rne_of_isRep h.1, h.2]

/-- Rounding a value bounded by a finite value of the format gives a finite value. -/
theorem round_of_abs_le {x B : ℝ} (hB : Ok φ B) (h : |x| ≤ B) :
    F64.round φ x = fin (φ.rne x) ∧ Ok φ (φ.rne x) ∧ |φ.rne x| ≤ B := by
  have h1 := Fmt.abs_rne_le hB.1 h
  have h2 : |φ.rne x| ≤ φ.maxFinite := h1.trans (le_abs_self B |>.trans hB.2)
  exact ⟨by simp [F64.round, h2], ⟨Fmt.rne_isRep x, h2⟩, h1⟩

/-- A value of the format at least `2 ^ e` in magnitude is a multiple of the spacing
`2 ^ (e + 1 - p)` of the binade `[2 ^ e, 2 ^ (e + 1))`. -/
theorem isRep_mul_ulp {a : ℝ} {e : ℤ} (ha : φ.IsRep a) (he : (2 : ℝ) ^ e ≤ |a|)
    (_hq : φ.qmin ≤ e + 1 - φ.p) : ∃ k : ℤ, a = k * 2 ^ (e + 1 - φ.p) := by
  obtain ⟨m, e', hm, he', rfl⟩ := ha
  rcases le_or_gt (e + 1 - φ.p) e' with h | h
  · refine ⟨m * 2 ^ (e' - (e + 1 - φ.p)).toNat, ?_⟩
    have : (2 : ℝ) ^ e' = 2 ^ ((e' - (e + 1 - φ.p)).toNat : ℤ) * 2 ^ (e + 1 - φ.p) := by
      rw [← zpow_add₀ (by norm_num)]; congr 1; omega
    rw [this, zpow_natCast]; push_cast; ring
  · -- `|a| ≤ 2 ^ p 2 ^ e' ≤ 2 ^ e ≤ |a|`, so `a = ±2 ^ e`
    have hm' : |(m : ℝ)| ≤ 2 ^ φ.p := by exact_mod_cast hm
    have h1 : |(m : ℝ) * 2 ^ e'| ≤ 2 ^ e := by
      rw [abs_mul, abs_of_pos (Fmt.two_zpow_pos e')]
      calc |(m : ℝ)| * 2 ^ e' ≤ 2 ^ φ.p * 2 ^ e' :=
            mul_le_mul_of_nonneg_right hm' (Fmt.two_zpow_pos e').le
        _ = 2 ^ ((φ.p : ℤ) + e') := by rw [zpow_add₀ (by norm_num), zpow_natCast]
        _ ≤ 2 ^ e := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have heq : |(m : ℝ) * 2 ^ e'| = 2 ^ e := le_antisymm h1 he
    have hp := φ.hp
    have hp1 : (2 : ℝ) ^ e = ((2 ^ (φ.p - 1) : ℤ) : ℝ) * 2 ^ (e + 1 - φ.p) := by
      push_cast
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ φ.p)]; ring
    rcases abs_cases ((m : ℝ) * 2 ^ e') with ⟨h2, _⟩ | ⟨h2, _⟩
    · exact ⟨2 ^ (φ.p - 1), by rw [← hp1, ← heq, h2]⟩
    · refine ⟨-(2 ^ (φ.p - 1)), ?_⟩
      have : (m : ℝ) * 2 ^ e' = -2 ^ e := by linarith
      rw [this, hp1]; push_cast; ring

end Lemmas

/-! ## Invariants of the loop -/

/-- Values that `np.linalg.norm` can produce from finite rows: finite and non-negative, or `+inf`. -/
def NN (φ : Fmt) : F64 → Prop
  | fin a => Ok φ a ∧ 0 ≤ a
  | inf neg => neg = false
  | nan => False

/-- Floats whose finite values are in the format. -/
def Fine (φ : Fmt) (v : F64) : Prop := ∀ a, v = fin a → Ok φ a

section Invariants

variable {φ : Fmt}

theorem round_fine (x : ℝ) : Fine φ (F64.round φ x) := by
  intro a h
  unfold F64.round at h
  split_ifs at h with h1
  · cases h; exact ⟨Fmt.rne_isRep x, h1⟩

theorem nanToNum_ok {v : F64} (h : Fine φ v) : Ok φ (nanToNum φ v) := by
  match v with
  | fin a => exact h a rfl
  | inf false => exact ok_max
  | inf true => exact ok_neg_max
  | nan => exact ok_zero

theorem subR_fine (a : F64) (o : ℝ) : Fine φ (F64.subR φ a o) := by
  match a with
  | fin a => exact round_fine _
  | inf s => intro _ h; cases h
  | nan => intro _ h; cases h

theorem round_nn {x : ℝ} (hx : 0 ≤ x) : NN φ (F64.round φ x) := by
  unfold F64.round
  split_ifs with h
  · exact ⟨⟨Fmt.rne_isRep x, h⟩, Fmt.rne_zero (φ := φ) ▸ Fmt.rne_mono hx⟩
  · simp [NN]; linarith

theorem add_nn {u v : F64} (hu : NN φ u) (hv : NN φ v) : NN φ (F64.add φ u v) := by
  match u, v with
  | fin a, fin b => exact round_nn (add_nonneg hu.2 hv.2)
  | inf s, fin _ => exact hu
  | fin _, inf s => exact hv
  | inf s, inf t =>
    simp only [NN] at hu hv; subst hu hv; simp [F64.add, NN]
  | nan, _ => exact hu.elim
  | fin _, nan => exact hv.elim
  | inf _, nan => exact hv.elim

theorem eval_nn {xs : List F64} (h : ∀ v ∈ xs, NN φ v) (t : STree) : NN φ (t.eval φ xs) := by
  induction t with
  | leaf i =>
    simp only [STree.eval, List.getD_eq_getElem?_getD]
    cases hi : xs[i]? with
    | none => exact ⟨ok_zero, le_rfl⟩
    | some v => exact h v (List.mem_of_getElem? hi)
  | node l r ihl ihr => exact add_nn ihl ihr

theorem reduce_nn {P : Plan} {xs : List F64} (h : ∀ v ∈ xs, NN φ v) : NN φ (reduce φ P xs) := by
  unfold reduce
  split_ifs
  · exact ⟨ok_zero, le_rfl⟩
  · exact eval_nn h _

theorem rowNorm_nn {P : Plan} {o : Ord} {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) :
    NN φ (rowNorm φ P o (r.map fin)) := by
  cases o with
  | l1 =>
    apply reduce_nn
    simp only [List.map_map, List.mem_map, Function.comp, F64.abs]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨isRep_abs (hr a ha).1, by rw [abs_abs]; exact (hr a ha).2⟩, abs_nonneg a⟩
  | l2 =>
    have hs := reduce_nn (φ := φ) (P := P) (xs := (r.map fin).map (F64.sq φ)) (by
      simp only [List.map_map, List.mem_map, Function.comp, F64.sq]
      rintro _ ⟨a, _, rfl⟩
      exact round_nn (mul_self_nonneg a))
    simp only [rowNorm]
    generalize reduce φ P ((r.map fin).map (F64.sq φ)) = s at hs
    match s with
    | fin a =>
      simp only [F64.sqrt, show ¬ a < 0 from not_lt.mpr hs.2, ite_false]
      exact round_nn (Real.sqrt_nonneg a)
    | inf b => simp only [NN] at hs; subst hs; exact rfl
    | nan => exact hs.elim

theorem nanToNum_nn {v : F64} (h : NN φ v) : Ok φ (nanToNum φ v) ∧ 0 ≤ nanToNum φ v := by
  match v with
  | fin a => exact h
  | inf b =>
    simp only [NN] at h; subst h
    exact ⟨ok_max, Fmt.maxFinite_pos.le⟩
  | nan => exact h.elim

end Invariants

namespace Clamp

variable {φ : Fmt} (C : Clamp φ)

theorem cur_ok {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) : Ok φ (C.cur r) ∧ 0 ≤ C.cur r :=
  nanToNum_nn (rowNorm_nn hr)

theorem one_le_factor (r : List ℝ) : 1 ≤ C.factor r := le_max_right _ _

theorem factor_ok {r : List ℝ} : Ok φ (C.factor r) := by
  unfold factor
  rcases le_total (nanToNum φ (F64.div φ (C.cur r) C.bound)) 1 with h | h
  · rw [max_eq_right h]; exact ok_one
  · rw [max_eq_left h]; exact nanToNum_ok (round_fine _)

/-- Dividing a finite value by the factor (at least 1) gives a finite value, no larger. -/
theorem div_factor {a : ℝ} (ha : Ok φ a) (r : List ℝ) :
    F64.div φ a (C.factor r) = fin (φ.rne (a / C.factor r)) ∧ Ok φ (φ.rne (a / C.factor r))
      ∧ |φ.rne (a / C.factor r)| ≤ |a| := by
  have hf := C.one_le_factor r
  have hB : Ok φ |a| := ⟨isRep_abs ha.1, by rw [abs_abs]; exact ha.2⟩
  have : |a / C.factor r| ≤ |a| := by
    rw [abs_div, abs_of_pos (show 0 < C.factor r by linarith)]
    exact div_le_self (abs_nonneg a) hf
  exact round_of_abs_le hB this

theorem body_ok {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) : ∀ a ∈ C.body r, Ok φ a := by
  simp only [body, List.mem_map]
  rintro _ ⟨a, ha, rfl⟩
  rw [(C.div_factor (hr a ha) r).1]
  exact (C.div_factor (hr a ha) r).2.1

theorem iterate_ok {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) (N : ℕ) : ∀ a ∈ C.body^[N] r, Ok φ a := by
  induction N generalizing r with
  | zero => exact hr
  | succ N ih => rw [Function.iterate_succ_apply]; exact ih (C.body_ok hr)

/-- A row within the bound is left unchanged by the loop: its factor rounds to at most 1. -/
theorem body_eq_self (hb : 0 < C.bound) {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) (h : ¬ C.above r) :
    C.body r = r := by
  have hc := C.cur_ok hr
  have hle : C.cur r ≤ C.bound := not_lt.mp h
  have hq0 : 0 ≤ C.cur r / C.bound := div_nonneg hc.2 hb.le
  have hq1 : C.cur r / C.bound ≤ 1 := (div_le_one hb).mpr hle
  have hround := round_of_abs_le (φ := φ) ok_one (by rw [abs_of_nonneg hq0]; exact hq1)
  have hrne1 : φ.rne (C.cur r / C.bound) ≤ 1 := Fmt.rne_le_of_le isRep_one hq1
  have hf : C.factor r = 1 := by
    simp only [factor, F64.div, hround.1, nanToNum]
    exact max_eq_right hrne1
  have hmap : ∀ a ∈ r, toR (F64.div φ a (C.factor r)) = a := by
    intro a ha
    rw [hf, F64.div, div_one, round_of_ok (hr a ha), toR]
  conv_rhs => rw [← List.map_id r]
  exact List.map_congr_left hmap

/-- Once a row is within the bound, further passes leave it unchanged. -/
theorem iterate_fixed (hb : 0 < C.bound) {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) {N : ℕ}
    (h : ¬ C.above (C.body^[N] r)) : ∀ M, N ≤ M → C.body^[M] r = C.body^[N] r := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => rfl
  | succ M _ ih =>
    rw [Function.iterate_succ_apply', ih]
    exact C.body_eq_self hb (C.iterate_ok hr N) h

open Classical in
/-- The clamped row: the row after the first pass that brings it within the bound. -/
noncomputable def res (r : List ℝ) : List ℝ :=
  if h : ∃ N, ¬ C.above (C.body^[N] r) then C.body^[Nat.find h] r else r

theorem res_eq (hb : 0 < C.bound) {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) {N : ℕ}
    (h : ¬ C.above (C.body^[N] r)) : C.body^[N] r = C.res r := by
  classical
  have hex : ∃ N, ¬ C.above (C.body^[N] r) := ⟨N, h⟩
  simp only [res, hex, dite_eq_left]
  exact C.iterate_fixed hb hr (Nat.find_spec hex) N (Nat.find_min' hex h)

theorem loop_spec {n : ℕ} {rows out : List (List ℝ)} (h : C.loop n rows = some out) :
    ∃ N, out = rows.map (C.body^[N]) ∧ ∀ r ∈ out, ¬ C.above r := by
  induction n generalizing rows with
  | zero =>
    simp only [loop] at h
    split_ifs at h with h1
    cases h
    push Not at h1
    exact ⟨0, by simp, h1⟩
  | succ n ih =>
    simp only [loop] at h
    split_ifs at h with h1
    · obtain ⟨N, rfl, h2⟩ := ih h
      refine ⟨N + 1, ?_, h2⟩
      simp only [List.map_map]
      congr 1
    · cases h
      push Not at h1
      exact ⟨0, by simp, h1⟩

theorem pre_ok (row : List F64) : ∀ a ∈ C.pre row, Ok φ a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  simp only [pre, List.getElem_zipWith]
  exact nanToNum_ok (subR_fine _ _)

/-- **Rows are clamped independently.** Although the loop runs over the whole array until every
row is within the bound, each output row depends only on the corresponding input row. -/
theorem clamp_map (hb : 0 < C.bound) {n : ℕ} {x out : List (List F64)}
    (h : C.clamp n x = .ok out) : out = x.map (fun row => C.post (C.res (C.pre row))) := by
  unfold clamp at h
  split at h
  · rename_i rows hl
    cases h
    obtain ⟨N, rfl, habove⟩ := C.loop_spec hl
    simp only [List.map_map]
    apply List.map_congr_left
    intro row hrow
    simp only [Function.comp]
    congr 1
    exact C.res_eq hb (C.pre_ok row) (habove _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨row, hrow, rfl⟩, rfl⟩))
  · cases h

end Clamp

/-! ## Stability -/

open Classical in
/-- The symmetric distance between two datasets: the size of the symmetric difference of their
multisets of rows. -/
noncomputable def symDist {α : Type*} (x y : List α) : ℕ :=
  Multiset.card ((x : Multiset α) - (y : Multiset α)) + Multiset.card ((y : Multiset α) - (x : Multiset α))

theorem card_map_sub_le {α β : Type*} [DecidableEq α] [DecidableEq β] (g : α → β)
    (s t : Multiset α) : Multiset.card (s.map g - t.map g) ≤ Multiset.card (s - t) := by
  have h1 : s.map g ≤ (s - t).map g + t.map g := by
    rw [← Multiset.map_add]; exact Multiset.map_le_map le_tsub_add
  calc Multiset.card (s.map g - t.map g) ≤ Multiset.card ((s - t).map g) :=
        Multiset.card_le_card (tsub_le_iff_right.mpr h1)
    _ = Multiset.card (s - t) := Multiset.card_map _ _

/-- A row-by-row map is 1-stable under the symmetric distance. -/
theorem symDist_map_le {α β : Type*} (g : α → β) (x y : List α) :
    symDist (x.map g) (y.map g) ≤ symDist x y := by
  classical
  unfold symDist
  rw [← Multiset.map_coe, ← Multiset.map_coe]
  exact add_le_add (card_map_sub_le g _ _) (card_map_sub_le g _ _)

namespace Clamp

variable {φ : Fmt} (C : Clamp φ)

/-- **Stability.** On datasets where `_function` returns, the output datasets are no farther
apart under the symmetric distance than the inputs: the stability map `d_in ↦ d_in` is sound. -/
theorem clamp_stable (hb : 0 < C.bound) {n n' : ℕ} {x x' out out' : List (List F64)}
    (h : C.clamp n x = .ok out) (h' : C.clamp n' x' = .ok out') :
    symDist out out' ≤ symDist x x' := by
  rw [C.clamp_map hb h, C.clamp_map hb h']
  exact symDist_map_le _ x x'

theorem mem_zipWith_round {r : List ℝ} {os : List ℝ} {v : F64}
    (h : v ∈ List.zipWith (fun a o => F64.round φ (a + o)) r os) : ∃ y, v = F64.round φ y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp only [List.getElem_zipWith]
  exact ⟨_, rfl⟩

/-- **No NaN.** Outputs never contain NaN. -/
theorem clamp_no_nan {n : ℕ} {x out : List (List F64)} (h : C.clamp n x = .ok out) :
    ∀ row ∈ out, ∀ v ∈ row, v ≠ nan := by
  unfold clamp at h
  split at h
  · cases h
    simp only [List.mem_map]
    rintro _ ⟨r, _, rfl⟩ v hv
    unfold post at hv
    split_ifs at hv
    · obtain ⟨o, _, rfl⟩ := List.mem_map.mp hv
      simp
    · obtain ⟨y, rfl⟩ := mem_zipWith_round (φ := φ) hv
      unfold F64.round
      split_ifs <;> simp
  · cases h

theorem zipWith_zeros {α : Type*} (f : α → ℝ → F64) {r : List α} {d : ℕ} (hd : r.length ≤ d) :
    List.zipWith f r (List.replicate d 0) = r.map (f · 0) := by
  induction r generalizing d with
  | nil => simp
  | cons a r ih =>
    cases d with
    | zero => simp at hd
    | succ d =>
      simp only [List.replicate_succ, List.zipWith_cons_cons, List.map_cons]
      rw [ih (by simp at hd; omega)]

end Clamp


/-! ## Exact sums -/

section Exact

variable {φ : Fmt}

theorem leaves_length_pos (t : STree) : 0 < t.leaves.length := by
  induction t with
  | leaf i => simp [STree.leaves]
  | node l r ihl _ => simp only [STree.leaves, List.length_append]; omega

/-- The tree of a one-element row is a leaf. -/
theorem tree_one (P : Plan) : P.tree 1 = .leaf 0 := by
  have h := P.perm 1 one_pos
  match ht : P.tree 1 with
  | .leaf i =>
    rw [ht] at h
    simp only [STree.leaves, List.range_one] at h
    rw [List.singleton_perm_singleton.mp h]
  | .node l r =>
    rw [ht] at h
    have := h.length_eq
    simp only [STree.leaves, List.length_append, List.length_range] at this
    have := leaves_length_pos l; have := leaves_length_pos r; omega

/-- The tree of a two-element row adds its two elements. -/
theorem tree_two (P : Plan) (xs : List F64) (v : F64) (hx : xs = [v, v]) :
    (P.tree 2).eval φ xs = F64.add φ v v := by
  have h := P.perm 2 two_pos
  match ht : P.tree 2 with
  | .leaf i =>
    rw [ht] at h; have := h.length_eq; simp [STree.leaves] at this
  | .node l r =>
    rw [ht] at h
    have hlen := h.length_eq
    simp only [STree.leaves, List.length_append, List.length_range] at hlen
    have hl := leaves_length_pos l; have hr := leaves_length_pos r
    have hmem : ∀ i ∈ l.leaves ++ r.leaves, i < 2 := fun i hi => List.mem_range.mp (h.subset hi)
    have hv : ∀ i, i < 2 → xs.getD i (fin 0) = v := by
      intro i hi; subst hx; interval_cases i <;> rfl
    have h1 : ∀ t : STree, t.leaves.length = 1 → (∀ i ∈ t.leaves, i < 2) → t.eval φ xs = v := by
      intro t ht1 htm
      match t with
      | .leaf i => exact hv i (htm i (by simp [STree.leaves]))
      | .node a b =>
        simp only [STree.leaves, List.length_append] at ht1
        have := leaves_length_pos a; have := leaves_length_pos b; omega
    simp only [STree.eval]
    rw [h1 l (by omega) (fun i hi => hmem i (List.mem_append_left _ hi)),
      h1 r (by omega) (fun i hi => hmem i (List.mem_append_right _ hi))]

/-- A tree over values that are natural multiples of `2 ^ c` sums them exactly when the total
is in the format. -/
theorem eval_exact {c : ℤ} (hc : φ.qmin ≤ c) (ks : List ℕ) (t : STree)
    (hS : (t.leaves.map (ks.getD · 0)).sum ≤ 2 ^ φ.p)
    (hM : ((t.leaves.map (ks.getD · 0)).sum : ℝ) * 2 ^ c ≤ φ.maxFinite) :
    t.eval φ (ks.map fun k : ℕ => fin ((k : ℝ) * 2 ^ c)) =
      fin (((t.leaves.map (ks.getD · 0)).sum : ℝ) * 2 ^ c) := by
  induction t with
  | leaf i =>
    simp only [STree.eval, STree.leaves, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ks[i]? <;> simp
  | node l r ihl ihr =>
    simp only [STree.leaves, List.map_append, List.sum_append] at hS hM ⊢
    generalize (l.leaves.map (ks.getD · 0)).sum = A at *
    generalize (r.leaves.map (ks.getD · 0)).sum = B at *
    have h2 := Fmt.two_zpow_pos c
    have hl := ihl (by omega) (le_trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_add_right A B) h2.le) hM)
    have hr := ihr (by omega) (le_trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.le_add_left B A) h2.le) hM)
    simp only [STree.eval, hl, hr, F64.add]
    rw [← add_mul, show (A : ℝ) + B = ((A + B : ℕ) : ℝ) by push_cast; ring]
    apply round_of_ok
    refine ⟨?_, by rw [abs_of_nonneg (by positivity)]; exact hM⟩
    have := Fmt.isRep_of_mul (φ := φ) (k := ((A + B : ℕ) : ℤ))
      (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hS) hc
    rwa [Int.cast_natCast] at this

theorem sum_getD_range (ks : List ℕ) : ((List.range ks.length).map (ks.getD · 0)).sum = ks.sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

/-- `add.reduce` of natural multiples of `2 ^ c` is exact when the total is in the format. -/
theorem reduce_exact (P : Plan) {c : ℤ} (hc : φ.qmin ≤ c) (ks : List ℕ) (hne : ks ≠ [])
    (hS : ks.sum ≤ 2 ^ φ.p) (hM : (ks.sum : ℝ) * 2 ^ c ≤ φ.maxFinite) :
    reduce φ P (ks.map fun k : ℕ => fin ((k : ℝ) * 2 ^ c)) = fin ((ks.sum : ℝ) * 2 ^ c) := by
  have hpos : 0 < ks.length := List.length_pos_iff.mpr hne
  have hperm := P.perm ks.length hpos
  have hsum : ((P.tree ks.length).leaves.map (ks.getD · 0)).sum = ks.sum := by
    rw [(hperm.map _).sum_eq, sum_getD_range]
  have hne' : (ks.map fun k : ℕ => fin ((k : ℝ) * 2 ^ c)) ≠ [] := by simpa using hne
  unfold reduce
  rw [ite_eq_right hne', List.length_map, eval_exact hc ks _ (hsum ▸ hS) (hsum ▸ hM), hsum]

/-- `add.reduce` of zeros is zero. -/
theorem reduce_zeros (P : Plan) (xs : List F64) (h : ∀ v ∈ xs, v = fin 0) :
    reduce φ P xs = fin 0 := by
  unfold reduce
  split_ifs
  · rfl
  · generalize P.tree xs.length = t
    induction t with
    | leaf i =>
      simp only [STree.eval, List.getD_eq_getElem?_getD]
      cases hi : xs[i]? with
      | none => rfl
      | some v => exact h v (List.mem_of_getElem? hi)
    | node l r ihl ihr =>
      simp only [STree.eval, ihl, ihr, F64.add, add_zero]
      exact round_of_ok ok_zero

/-- Rounding to the subnormal grid: a value within half a step of a grid point `k 2 ^ qmin` of
the format rounds to it. -/
theorem rne_near_grid {x : ℝ} {k : ℤ} (hk : φ.IsRep (k * 2 ^ φ.qmin))
    (h : |x - k * 2 ^ φ.qmin| < 2 ^ φ.qmin / 2) : φ.rne x = k * 2 ^ φ.qmin := by
  apply rne_eq_of_closer hk
  intro s hs hne
  obtain ⟨j, rfl⟩ := Fmt.isRep_mul_qmin hs
  have ht := Fmt.two_zpow_pos φ.qmin
  have hjk : j ≠ k := fun h' => hne (by rw [h'])
  have h1 : (1 : ℝ) ≤ |(j : ℝ) - k| := by
    have : (1 : ℤ) ≤ |j - k| := Int.one_le_abs (sub_ne_zero.mpr hjk)
    exact_mod_cast this
  have h2 : 2 ^ φ.qmin ≤ |(j : ℝ) * 2 ^ φ.qmin - k * 2 ^ φ.qmin| := by
    rw [← sub_mul, abs_mul, abs_of_pos ht]; nlinarith
  have := abs_sub_abs_le_abs_sub ((j : ℝ) * 2 ^ φ.qmin - k * 2 ^ φ.qmin) (x - k * 2 ^ φ.qmin)
  rw [show (j : ℝ) * 2 ^ φ.qmin - k * 2 ^ φ.qmin - (x - k * 2 ^ φ.qmin) = -(x - j * 2 ^ φ.qmin)
    by ring, abs_neg] at this
  linarith

end Exact

/-! ## Counterexamples -/

section Counterexamples

-- the counterexamples evaluate powers of two up to `2 ^ 1074`
set_option exponentiation.threshold 2200

theorem q64 : binary64.qmin = -1074 := by decide

theorem p64 : binary64.p = 53 := rfl

theorem max64 : binary64.maxFinite = (2 ^ 53 - 1) * 2 ^ 971 := by
  simp only [Fmt.maxFinite, Fmt.qtop, binary64]
  rw [show (1023 : ℤ) - (53 : ℕ) + 1 = (971 : ℕ) by norm_num, zpow_natCast]

/-- Integer multiples of powers of two in the `f64` range. -/
theorem ok64 (n : ℤ) (c : ℤ) (hn : |n| ≤ 2 ^ 53) (hc : -1074 ≤ c) (hb : |(n : ℝ) * 2 ^ c| ≤ binary64.maxFinite) :
    Ok binary64 (n * 2 ^ c) :=
  ⟨Fmt.isRep_of_mul (φ := binary64) (by rw [p64]; exact_mod_cast hn) (by rw [q64]; exact hc), hb⟩

theorem ok64_int (n : ℤ) (hn : |n| ≤ 2 ^ 53) : Ok binary64 n := by
  have := ok64 n 0 hn (by norm_num) (by
    rw [max64, zpow_zero, mul_one]
    have : |(n : ℝ)| ≤ 2 ^ 53 := by exact_mod_cast hn
    have : (2 : ℝ) ^ 53 ≤ (2 ^ 53 - 1) * 2 ^ 971 := by norm_num
    linarith)
  simpa using this


theorem round_eq {φ : Fmt} {x r : ℝ} (h : φ.rne x = r) (hr : |r| ≤ φ.maxFinite) :
    F64.round φ x = fin r := by
  simp [F64.round, h, hr]

theorem sqrt_sq_eq {a : ℝ} (ha : 0 ≤ a) : Real.sqrt (a * a) = a := Real.sqrt_mul_self ha

/-- The L2 norm of a one-element row `[a]` with `a * a` and `a` exact. -/
theorem rowNorm_single {φ : Fmt} (P : Plan) {a : ℝ} (ha : 0 ≤ a) (h1 : Ok φ (a * a)) (h2 : Ok φ a) :
    rowNorm φ P .l2 [fin a] = fin a := by
  simp only [rowNorm, List.map_cons, List.map_nil, F64.sq, round_of_ok h1, reduce,
    List.cons_ne_nil, ite_false, List.length_singleton, tree_one, STree.eval]
  simp only [List.getD_cons_zero, F64.sqrt, show ¬ a * a < 0 from not_lt.mpr (mul_self_nonneg a),
    ite_false, sqrt_sq_eq ha, round_of_ok h2]

/-- **F9 (origin rounding).** `arg + origin` rounds: with `origin = [2^56]` and `norm = 12`, the
row `[2^56 + 48]` is clamped to `[2^56 + 12]`, which rounds to `[2^56 + 16]` (floats near `2^56`
are 16 apart). The output row is 16 from the origin, so it fails the output domain's norm check
(`p = 2`; the one-column case is the same for `p = 1`). -/
theorem origin_rounding (P : Plan) :
    let C : Clamp binary64 := ⟨P, .l2, 12, [2 ^ 56]⟩
    C.clampV0 2 [[fin (2 ^ 56 + 48)]] = .ok [[fin (2 ^ 56 + 16)]] ∧
      ¬ C.memberNorm [fin (2 ^ 56 + 16)] := by
  intro C
  have o48 := ok64_int 48 (by norm_num)
  have o2304 := ok64_int 2304 (by norm_num)
  have o4 := ok64_int 4 (by norm_num)
  have o12 := ok64_int 12 (by norm_num)
  have o144 := ok64_int 144 (by norm_num)
  have o16 := ok64_int 16 (by norm_num)
  have o256 := ok64_int 256 (by norm_num)
  push_cast at o48 o2304 o4 o12 o144 o16 o256
  have n48 : rowNorm binary64 P .l2 [fin 48] = fin 48 :=
    rowNorm_single P (by norm_num) (by norm_num; exact o2304) o48
  have n12 : rowNorm binary64 P .l2 [fin 12] = fin 12 :=
    rowNorm_single P (by norm_num) (by norm_num; exact o144) o12
  have n16 : rowNorm binary64 P .l2 [fin 16] = fin 16 :=
    rowNorm_single P (by norm_num) (by norm_num; exact o256) o16
  -- `2^56 + 12` rounds to `2^56 + 16`
  have hr : binary64.rne (12 + 2 ^ 56) = 2 ^ 56 + 16 := by
    have hf : binary64.fexp (12 + 2 ^ 56) = 4 := by
      rw [Fmt.fexp_of_bounds (e := 56)] <;> simp [p64, q64] <;> norm_num [abs_of_pos]
    unfold Fmt.rne
    rw [hf]
    have : roundEven ((12 + 2 ^ 56) / 2 ^ (4 : ℤ)) = 2 ^ 52 + 1 := by
      apply roundEven_eq; left; norm_num [abs_of_pos]
    rw [this]; norm_num
  have hpost : F64.round binary64 (12 + 2 ^ 56) = fin (2 ^ 56 + 16) :=
    round_eq hr (by rw [max64]; norm_num [abs_of_pos])
  have hpre : C.pre [fin (2 ^ 56 + 48)] = [48] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR,
      show (2 : ℝ) ^ 56 + 48 - 2 ^ 56 = 48 by ring, round_of_ok o48, nanToNum]
  have hc48 : C.cur [48] = 48 := by simp [Clamp.cur, C, n48, nanToNum]
  have hc12 : C.cur [12] = 12 := by simp [Clamp.cur, C, n12, nanToNum]
  have hbody : C.body [48] = [12] := by
    have hf : C.factor [48] = 4 := by
      simp only [Clamp.factor, hc48, C, F64.div, show (48 : ℝ) / 12 = 4 by norm_num,
        round_of_ok o4, nanToNum]
      norm_num
    simp only [Clamp.body, hf, List.map_cons, List.map_nil, F64.div,
      show (48 : ℝ) / 4 = 12 by norm_num, round_of_ok o12, toR]
  have hloop : C.loop 2 [[48]] = some [[12]] := by
    have a1 : ∃ r ∈ [[(48 : ℝ)]], C.above r := ⟨[48], by simp, by
      simp only [Clamp.above, hc48, C]; norm_num⟩
    have a2 : ¬ ∃ r ∈ [[(12 : ℝ)]], C.above r := by
      simp only [List.mem_singleton, exists_eq_left, Clamp.above, hc12, C]; norm_num
    simp only [Clamp.loop, a1, ite_true, List.map_cons, List.map_nil, hbody, a2, ite_false]
  refine ⟨?_, ?_⟩
  · simp only [Clamp.clampV0, List.cons_ne_nil, ite_false, List.map_cons, List.map_nil, hpre, hloop,
      Clamp.postV0, C, List.zipWith_cons_cons, List.zipWith_nil_left, hpost]
  · simp only [Clamp.memberNorm, Clamp.outside, C, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR,
      show (2 : ℝ) ^ 56 + 16 - 2 ^ 56 = 16 by ring, round_of_ok o16, n16, F64.gt, not_not]
    norm_num


/-- A row of zeros has norm zero. -/
theorem rowNorm_zeros {φ : Fmt} (P : Plan) (o : Ord) (xs : List F64) (h : ∀ v ∈ xs, v = fin 0) :
    rowNorm φ P o xs = fin 0 := by
  cases o with
  | l1 =>
    apply reduce_zeros
    simp only [List.mem_map]
    rintro _ ⟨v, hv, rfl⟩; rw [h v hv]; simp [F64.abs]
  | l2 =>
    simp only [rowNorm]
    rw [reduce_zeros]
    · simp [F64.sqrt, round_of_ok ok_zero]
    · simp only [List.mem_map]
      rintro _ ⟨v, hv, rfl⟩; rw [h v hv]; simp [F64.sq, round_of_ok ok_zero]

/-- A loop whose rows include one above the bound, and which a pass leaves unchanged, runs out of
any fuel. -/
theorem loop_stuck {φ : Fmt} (C : Clamp φ) {rows : List (List ℝ)} (ha : ∃ r ∈ rows, C.above r)
    (hb : rows.map C.body = rows) : ∀ n, C.loop n rows = none := by
  intro n
  induction n with
  | zero => simp [Clamp.loop, ha]
  | succ n ih => simp only [Clamp.loop, ha, ite_true, hb, ih]

/-- The L1 norm of a row of natural multiples of `2 ^ c` is exact when the total is in the format. -/
theorem cur_l1 {φ : Fmt} (C : Clamp φ) (hC : C.ord = .l1) {c : ℤ} (hc : φ.qmin ≤ c) (ks : List ℕ)
    (hne : ks ≠ []) (hS : ks.sum ≤ 2 ^ φ.p) (hM : (ks.sum : ℝ) * 2 ^ c ≤ φ.maxFinite) :
    C.cur (ks.map fun k : ℕ => (k : ℝ) * 2 ^ c) = ks.sum * 2 ^ c := by
  have e : ((ks.map fun k : ℕ => (k : ℝ) * 2 ^ c).map fin).map F64.abs =
      ks.map fun k : ℕ => fin ((k : ℝ) * 2 ^ c) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp, F64.abs]
    rw [abs_of_nonneg (by positivity)]
  simp only [Clamp.cur, rowNorm, hC, e, reduce_exact C.P hc ks hne hS hM, nanToNum]

/-- **F10 (underflow).** `np.linalg.norm(x, ord=2)` squares without scaling, so the squares of
small values underflow to zero: with `norm = 2^-600`, the row `[2^-565, 0]` has computed norm 0
and is output unchanged. It passes the domain's (equally affected) check, but its Euclidean norm
`2^-565` exceeds the bound. -/
theorem l2_underflow (P : Plan) :
    let C : Clamp binary64 := ⟨P, .l2, 2 ^ (-600 : ℤ), [0, 0]⟩
    C.clampV0 0 [[fin (2 ^ (-565 : ℤ)), fin 0]] = .ok [[fin (2 ^ (-565 : ℤ)), fin 0]] ∧
      C.memberNorm [fin (2 ^ (-565 : ℤ)), fin 0] ∧
      C.bound < Real.sqrt ((2 ^ (-565 : ℤ)) ^ 2 + 0 ^ 2) := by
  intro C
  have oa : Ok binary64 (2 ^ (-565 : ℤ)) := by
    have := ok64 1 (-565) (by norm_num) (by norm_num) (by rw [max64]; norm_num [abs_of_pos])
    simpa using this
  have hsq : F64.sq binary64 (fin (2 ^ (-565 : ℤ))) = fin 0 := by
    simp only [F64.sq]
    apply round_eq _ (by simp; exact Fmt.maxFinite_pos.le)
    apply rne_tiny
    rw [q64, ← zpow_add₀ (by norm_num)]; norm_num [abs_of_pos]
  have hsq0 : F64.sq binary64 (fin 0) = fin 0 := by simp [F64.sq, round_of_ok ok_zero]
  have hnorm : rowNorm binary64 P .l2 [fin (2 ^ (-565 : ℤ)), fin 0] = fin 0 := by
    simp only [rowNorm, List.map_cons, List.map_nil, hsq, hsq0]
    rw [reduce_zeros _ _ (by simp)]
    simp [F64.sqrt, round_of_ok ok_zero]
  have hpre : C.pre [fin (2 ^ (-565 : ℤ)), fin 0] = [2 ^ (-565 : ℤ), 0] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok oa, round_of_ok ok_zero, nanToNum]
  have hna : ¬ ∃ r ∈ [[(2 : ℝ) ^ (-565 : ℤ), 0]], C.above r := by
    simp only [List.mem_singleton, exists_eq_left, Clamp.above, Clamp.cur, List.map_cons,
      List.map_nil, C, hnorm, nanToNum, not_lt]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · simp only [Clamp.clampV0, List.cons_ne_nil, ite_false, List.map_cons, List.map_nil, hpre,
      Clamp.loop, hna, ite_false, Clamp.postV0, C, List.zipWith_cons_cons, List.zipWith_nil_left,
      add_zero, round_of_ok oa, round_of_ok ok_zero]
  · simp only [Clamp.memberNorm, Clamp.outside, C, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR,
      sub_zero, round_of_ok oa, round_of_ok ok_zero, hnorm, F64.gt, not_lt]
    positivity
  · simp only [C]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (by positivity)]
    exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)

/-- **F11 (non-termination).** The loop divides each element by a factor that can round back to
the same element. With `p = 1` and `norm = 3 · 2^-1074` (three times the smallest subnormal), the
row of four smallest subnormals has norm `4 · 2^-1074`, its factor rounds to a value in
`[1, 3/2]`, and dividing `2^-1074` by it rounds back to `2^-1074`: the loop never ends. -/
theorem nonterm_subnormal (P : Plan) (n : ℕ) :
    (⟨P, .l1, 3 * 2 ^ (-1074 : ℤ), [0, 0, 0, 0]⟩ : Clamp binary64).clampV0 n
      [[fin (2 ^ (-1074 : ℤ)), fin (2 ^ (-1074 : ℤ)), fin (2 ^ (-1074 : ℤ)), fin (2 ^ (-1074 : ℤ))]]
      = .diverge := by
  set t : ℝ := 2 ^ (-1074 : ℤ) with htdef
  set C : Clamp binary64 := ⟨P, .l1, 3 * t, [0, 0, 0, 0]⟩ with hCdef
  have ht : 0 < t := by positivity
  have ot : Ok binary64 t := by
    have := ok64 1 (-1074) (by norm_num) (by norm_num) (by rw [max64]; norm_num [abs_of_pos])
    rw [Int.cast_one, one_mul] at this; exact this
  have hrow : [t, t, t, t] = ([1, 1, 1, 1] : List ℕ).map fun k : ℕ => (k : ℝ) * 2 ^ (-1074 : ℤ) := by
    simp only [List.map_cons, List.map_nil, Nat.cast_one, one_mul, htdef]
  have hcur : C.cur [t, t, t, t] = 4 * t := by
    rw [hrow, cur_l1 C rfl (by rw [q64]) _ (by simp) (by simp [p64]) (by
      rw [max64]; norm_num [abs_of_pos])]
    norm_num
  -- the factor is `rne (4 / 3)`, in `[1, 3/2]`
  have o32 : Ok binary64 (3 / 2) := by
    have := ok64 3 (-1) (by norm_num) (by norm_num) (by rw [max64]; norm_num [abs_of_pos])
    norm_num at this; exact this
  set f := binary64.rne (4 / 3) with hfdef
  have hf1 : 1 ≤ f := Fmt.le_rne_of_le isRep_one (by norm_num)
  have hf2 : f ≤ 3 / 2 := Fmt.rne_le_of_le o32.1 (by norm_num)
  have hfac : C.factor [t, t, t, t] = f := by
    have hq : 4 * t / (3 * t) = 4 / 3 := by field_simp
    have hr := round_of_abs_le (x := 4 / 3) o32 (by norm_num [abs_of_pos])
    simp only [Clamp.factor, hcur, C, F64.div, hq, hr.1, nanToNum]
    exact max_eq_left hf1
  -- dividing `t` by it rounds back to `t`
  have hdiv : toR (F64.div binary64 t f) = t := by
    have hn : binary64.rne (t / f) = t := by
      have h1 : t / f ≤ t := div_le_self ht.le hf1
      have h2 : 2 * t / 3 ≤ t / f := by
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
      have := rne_near_grid (φ := binary64) (x := t / f) (k := 1)
        (by rw [q64, Int.cast_one, one_mul]; exact ot.1) (by
          rw [q64, Int.cast_one, one_mul, ← htdef, abs_of_nonpos (by linarith)]
          linarith)
      rw [q64, Int.cast_one, one_mul] at this; exact this
    rw [F64.div, round_eq hn ot.2]; rfl
  have hbody : C.body [t, t, t, t] = [t, t, t, t] := by
    simp only [Clamp.body, hfac, List.map_cons, List.map_nil, hdiv]
  have hpre : C.pre [fin t, fin t, fin t, fin t] = [t, t, t, t] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok ot, nanToNum]
  have habove : ∃ r ∈ [[t, t, t, t]], C.above r :=
    ⟨_, List.mem_singleton_self _, by simp only [Clamp.above, hcur, C]; linarith⟩
  have hloop := loop_stuck C habove (by simp [hbody]) n
  unfold Clamp.clampV0
  rw [ite_eq_right (by simp), List.map_singleton, hpre, hloop]

/-- Dividing `k t` by a factor `f` close to 1 moves it by less than half of `t`. -/
theorem stuck_div {k : ℕ} {t f : ℝ} (ht : 0 < t) (hf : 1 ≤ f) (h : (k : ℝ) * (f - 1) < f / 2) :
    |k * t / f - k * t| < t / 2 := by
  have hf0 : 0 < f := by linarith
  rw [show (k : ℝ) * t / f - k * t = -(k * (f - 1) * t / f) by field_simp; ring, abs_neg,
    abs_of_nonneg (by have : (0 : ℝ) ≤ f - 1 := by linarith
                      positivity), div_lt_iff₀ hf0]
  nlinarith

/-- **F11 (non-termination), with a normal bound.** For `p = 1`, the bound being a normal float
is not enough: with `norm = 2^-1022` (the smallest normal float), the row
`[A t, A t, 3 t]` (`t = 2^-1074`, `A = 2^51 - 1`) has norm `(2^52 + 1) t`, just above the bound;
its factor is `1 + 2^-52`, and dividing each element by it rounds back to the element. -/
theorem nonterm_normal (P : Plan) (n : ℕ) :
    (⟨P, .l1, 2 ^ (-1022 : ℤ), [0, 0, 0]⟩ : Clamp binary64).clampV0 n
      [[fin (2251799813685247 * 2 ^ (-1074 : ℤ)), fin (2251799813685247 * 2 ^ (-1074 : ℤ)),
        fin (3 * 2 ^ (-1074 : ℤ))]] = .diverge := by
  set t : ℝ := 2 ^ (-1074 : ℤ) with htdef
  set C : Clamp binary64 := ⟨P, .l1, 2 ^ (-1022 : ℤ), [0, 0, 0]⟩ with hCdef
  have ht : 0 < t := by positivity
  have okt : ∀ k : ℕ, k ≤ 2 ^ 53 → Ok binary64 (k * t) := by
    intro k hk
    have := ok64 k (-1074) (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hk) (by norm_num)
      (by rw [max64, abs_of_nonneg (by positivity)]
          have : (k : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hk
          calc (k : ℝ) * 2 ^ (-1074 : ℤ) ≤ 2 ^ 53 * 1 := by
                gcongr; exact zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
            _ ≤ _ := by norm_num)
    rwa [Int.cast_natCast] at this
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 2251799813685247 := ⟨_, rfl⟩
  have hAr : (A : ℝ) = 2251799813685247 := by rw [hA]; norm_num
  have oA := okt A (by rw [hA]; norm_num)
  have o3 : Ok binary64 (3 * t) := by have := okt 3 (by norm_num); push_cast at this; exact this
  have hrow : [(A : ℝ) * t, A * t, 3 * t] = ([A, A, 3] : List ℕ).map
      fun k : ℕ => (k : ℝ) * 2 ^ (-1074 : ℤ) := by
    simp only [List.map_cons, List.map_nil, htdef]; norm_num
  have hcur : C.cur [(A : ℝ) * t, A * t, 3 * t] = 4503599627370497 * t := by
    rw [hrow, cur_l1 C rfl (by rw [q64]) _ (by simp) (by simp [p64, hA]) (by
      rw [max64]; simp only [List.sum_cons, List.sum_nil, hA]; norm_num)]
    simp only [List.sum_cons, List.sum_nil, hA, htdef]; norm_num
  have hb : C.bound = 4503599627370496 * t := by
    simp only [C, htdef]; rw [show (4503599627370496 : ℝ) = 2 ^ (52 : ℤ) by norm_num,
      ← zpow_add₀ (by norm_num)]; norm_num
  -- the factor is exactly `1 + 2^-52`
  set f : ℝ := 4503599627370497 / 4503599627370496 with hfdef
  have of : Ok binary64 f := by
    have := ok64 4503599627370497 (-52) (by norm_num) (by norm_num) (by rw [max64]; norm_num [abs_of_pos])
    convert this using 1; rw [hfdef]; norm_num
  have hfac : C.factor [(A : ℝ) * t, A * t, 3 * t] = f := by
    have hq : 4503599627370497 * t / C.bound = f := by rw [hb, hfdef]; field_simp
    simp only [Clamp.factor, hcur, F64.div, hq, round_of_ok of, nanToNum]
    exact max_eq_left (by rw [hfdef]; norm_num)
  have hdiv : ∀ k : ℕ, Ok binary64 (k * t) → (k : ℝ) * (f - 1) < f / 2 →
      toR (F64.div binary64 (k * t) f) = k * t := by
    intro k hk hkf
    have hn : binary64.rne (k * t / f) = k * t := by
      have := rne_near_grid (φ := binary64) (x := k * t / f) (k := k)
        (by rw [q64, Int.cast_natCast]; exact hk.1)
        (by rw [q64, Int.cast_natCast]; exact stuck_div ht (by rw [hfdef]; norm_num) hkf)
      rwa [q64, Int.cast_natCast] at this
    rw [F64.div, round_eq hn hk.2]; rfl
  have hbody : C.body [(A : ℝ) * t, A * t, 3 * t] = [(A : ℝ) * t, A * t, 3 * t] := by
    have h3 := hdiv 3 (by exact_mod_cast o3) (by rw [hfdef]; norm_num)
    push_cast at h3
    simp only [Clamp.body, hfac, List.map_cons, List.map_nil,
      hdiv A oA (by rw [hAr, hfdef]; norm_num), h3]
  have hpre : C.pre [fin ((A : ℝ) * t), fin (A * t), fin (3 * t)] = [(A : ℝ) * t, A * t, 3 * t] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok oA, round_of_ok o3, nanToNum]
  have habove : ∃ r ∈ [[(A : ℝ) * t, A * t, 3 * t]], C.above r :=
    ⟨_, List.mem_singleton_self _, by simp only [Clamp.above, hcur, hb]; linarith⟩
  have hloop := loop_stuck C habove (by simp [hbody]) n
  unfold Clamp.clampV0
  rw [ite_eq_right (by simp), List.map_singleton, ← hAr, hpre, hloop]

/-- **F12 (overflow at the largest bound).** With `norm` the largest finite float and `p = 1`,
the row `[max, max]` has norm `+inf`, which `nan_to_num` turns into `max`: the loop sees the row
as within the bound and outputs it unchanged, but the domain's check computes the norm `+inf`. -/
theorem max_bound_overflow (φ : Fmt) (P : Plan) :
    let C : Clamp φ := ⟨P, .l1, φ.maxFinite, [0, 0]⟩
    C.clampV0 0 [[fin φ.maxFinite, fin φ.maxFinite]] = .ok [[fin φ.maxFinite, fin φ.maxFinite]] ∧
      ¬ C.memberNorm [fin φ.maxFinite, fin φ.maxFinite] := by
  intro C
  have hM := Fmt.maxFinite_pos (φ := φ)
  have h2M : φ.IsRep (φ.maxFinite + φ.maxFinite) := by
    have h1 : (1 : ℤ) ≤ 2 ^ φ.p := one_le_pow₀ (by norm_num)
    have := Fmt.isRep_of_mul (φ := φ) (k := 2 ^ φ.p - 1) (e := φ.qtop + 1)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by have := Fmt.qmin_le_qtop (φ := φ); omega)
    convert this using 1
    rw [Fmt.maxFinite_eq, zpow_add_one₀ (by norm_num)]; push_cast; ring
  have hadd : F64.add φ (fin φ.maxFinite) (fin φ.maxFinite) = inf false := by
    simp only [F64.add, F64.round, Fmt.rne_of_isRep h2M]
    rw [ite_eq_right (by rw [abs_of_pos (by linarith)]; linarith)]
    have : ¬ (φ.maxFinite + φ.maxFinite < 0) := by linarith
    simp [this]
  have hnorm : rowNorm φ P .l1 [fin φ.maxFinite, fin φ.maxFinite] = inf false := by
    simp only [rowNorm, List.map_cons, List.map_nil, F64.abs, abs_of_pos hM, reduce,
      List.cons_ne_nil, ite_false, List.length_cons, List.length_nil]
    rw [tree_two P _ (fin φ.maxFinite) rfl, hadd]
  have hpre : C.pre [fin φ.maxFinite, fin φ.maxFinite] = [φ.maxFinite, φ.maxFinite] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok ok_max, nanToNum]
  have hna : ¬ ∃ r ∈ [[φ.maxFinite, φ.maxFinite]], C.above r := by
    simp only [List.mem_singleton, exists_eq_left, Clamp.above, Clamp.cur, List.map_cons,
      List.map_nil, C, hnorm, nanToNum, lt_irrefl, not_false_eq_true]
  refine ⟨?_, ?_⟩
  · simp only [Clamp.clampV0, List.cons_ne_nil, ite_false, List.map_cons, List.map_nil, hpre,
      Clamp.loop, hna, ite_false, Clamp.postV0, C, List.zipWith_cons_cons, List.zipWith_nil_left,
      add_zero, round_of_ok ok_max]
  · simp only [Clamp.memberNorm, Clamp.outside, C, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR,
      sub_zero, round_of_ok ok_max, hnorm, F64.gt, not_true_eq_false, not_false_eq_true]

/-- **F13 (empty input).** `current_norm.max()` raises on an empty array, so `_function` raises on
the empty dataset, and returns on its neighbour with one row of zeros (at symmetric distance 1):
whether the dataset is empty is revealed exactly. -/
theorem empty_error {φ : Fmt} (C : Clamp φ) (hO : C.origin = [0]) (hb : 0 < C.bound) (n : ℕ) :
    C.clampV0 n [] = .error ∧ C.clampV0 0 [[fin 0]] = .ok [[fin 0]] ∧
      symDist ([] : List (List F64)) [[fin 0]] = 1 := by
  refine ⟨by simp [Clamp.clampV0], ?_, by simp [symDist]⟩
  have hpre : C.pre [fin 0] = [0] := by
    simp only [Clamp.pre, hO, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok ok_zero, nanToNum]
  have hna : ¬ ∃ r ∈ [[(0 : ℝ)]], C.above r := by
    simp only [List.mem_singleton, exists_eq_left, Clamp.above, Clamp.cur, List.map_cons,
      List.map_nil, rowNorm_zeros C.P C.ord [fin 0] (by simp), nanToNum, not_lt]
    exact hb.le
  simp only [Clamp.clampV0, List.cons_ne_nil, ite_false, List.map_cons, List.map_nil, hpre,
    Clamp.loop, hna, ite_false, Clamp.postV0, hO, List.zipWith_cons_cons, List.zipWith_nil_left,
    add_zero, round_of_ok ok_zero]

/-- **F14 (cardinalities).** The output domain keeps the input domain's `cardinalities`, but
clamping can increase the number of distinct values in a column: with `p = 1` and `norm = 1`,
`[[2, 0], [2, 2]]` (one distinct value in the first column) is clamped to
`[[1, 0], [1/2, 1/2]]` (two). -/
theorem cardinalities (P : Plan) :
    let C : Clamp binary64 := ⟨P, .l1, 1, [0, 0]⟩
    C.clampV0 1 [[fin 2, fin 0], [fin 2, fin 2]] = .ok [[fin 1, fin 0], [fin (1 / 2), fin (1 / 2)]] := by
  intro C
  have o1 := ok64_int 1 (by norm_num)
  have o2 := ok64_int 2 (by norm_num)
  have o4 := ok64_int 4 (by norm_num)
  have oh : Ok binary64 (1 / 2) := by
    have := ok64 1 (-1) (by norm_num) (by norm_num) (by rw [max64]; norm_num [abs_of_pos])
    norm_num at this; norm_num; exact this
  push_cast at o1 o2 o4
  have c20 : C.cur [2, 0] = 2 := by
    have := cur_l1 C rfl (c := 0) (by rw [q64]; norm_num) [2, 0] (by simp) (by simp [p64])
      (by rw [max64]; norm_num)
    norm_num at this; exact this
  have c22 : C.cur [2, 2] = 4 := by
    have := cur_l1 C rfl (c := 0) (by rw [q64]; norm_num) [2, 2] (by simp) (by simp [p64])
      (by rw [max64]; norm_num)
    norm_num at this; exact this
  have c10 : C.cur [1, 0] = 1 := by
    have := cur_l1 C rfl (c := 0) (by rw [q64]; norm_num) [1, 0] (by simp) (by simp [p64])
      (by rw [max64]; norm_num)
    norm_num at this; exact this
  have chh : C.cur [1 / 2, 1 / 2] = 1 := by
    have := cur_l1 C rfl (c := -1) (by rw [q64]; norm_num) [1, 1] (by simp) (by simp [p64])
      (by rw [max64]; norm_num)
    norm_num at this; norm_num; exact this
  have b20 : C.body [2, 0] = [1, 0] := by
    have hf : C.factor [2, 0] = 2 := by
      simp only [Clamp.factor, c20, C, F64.div, div_one, round_of_ok o2, nanToNum]; norm_num
    simp only [Clamp.body, hf, List.map_cons, List.map_nil, F64.div,
      show (2 : ℝ) / 2 = 1 by norm_num, zero_div, round_of_ok o1, round_of_ok ok_zero, toR]
  have b22 : C.body [2, 2] = [1 / 2, 1 / 2] := by
    have hf : C.factor [2, 2] = 4 := by
      simp only [Clamp.factor, c22, C, F64.div, div_one, round_of_ok o4, nanToNum]; norm_num
    simp only [Clamp.body, hf, List.map_cons, List.map_nil, F64.div,
      show (2 : ℝ) / 4 = 1 / 2 by norm_num, round_of_ok oh, toR]
  have hpre1 : C.pre [fin 2, fin 0] = [2, 0] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok o2, round_of_ok ok_zero, nanToNum]
  have hpre2 : C.pre [fin 2, fin 2] = [2, 2] := by
    simp only [C, Clamp.pre, List.zipWith_cons_cons, List.zipWith_nil_left, F64.subR, sub_zero,
      round_of_ok o2, nanToNum]
  have ha : ∃ r ∈ [[(2 : ℝ), 0], [2, 2]], C.above r :=
    ⟨[2, 0], by simp, by simp only [Clamp.above, c20, C]; norm_num⟩
  have hna : ¬ ∃ r ∈ [[(1 : ℝ), 0], [1 / 2, 1 / 2]], C.above r := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp, exists_eq_left,
      Clamp.above, c10, chh, C]; norm_num
  simp only [Clamp.clampV0, List.cons_ne_nil, ite_false, List.map_cons, List.map_nil, hpre1, hpre2,
    Clamp.loop, ha, ite_true, b20, b22, hna, ite_false, Clamp.postV0, C, List.zipWith_cons_cons,
    List.zipWith_nil_left, add_zero, round_of_ok o1, round_of_ok ok_zero, round_of_ok oh]

end Counterexamples


/-! ## Termination -/

section Termination

variable {φ : Fmt}

/-- The smallest exponent of normal floats. -/
def emin (φ : Fmt) : ℤ := 1 - φ.emax

theorem qmin_eq : φ.qmin = emin φ - φ.p + 1 := by unfold Fmt.qmin emin; ring

theorem two_pow_emax_le : (2 : ℝ) ^ φ.emax ≤ φ.maxFinite := by
  have hp := φ.hp
  have h1 : (2 : ℝ) ^ (φ.p - 1) ≤ 2 ^ φ.p - 1 := by
    have : (2 : ℝ) ^ φ.p = 2 * 2 ^ (φ.p - 1) := by rw [← pow_succ']; congr 1; omega
    have : (1 : ℝ) ≤ 2 ^ (φ.p - 1) := one_le_pow₀ (by norm_num)
    linarith
  have h2 : (2 : ℝ) ^ (φ.p - 1) * 2 ^ φ.qtop = 2 ^ φ.emax := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1
    unfold Fmt.qtop; push_cast [Nat.cast_sub (by omega : 1 ≤ φ.p)]; ring
  rw [← h2, Fmt.maxFinite_eq]
  exact mul_le_mul_of_nonneg_right h1 (Fmt.two_zpow_pos _).le

/-- Dividing a normal float by a factor at least `1 + 2^(1-p)` strictly decreases its magnitude:
the quotient is more than half a spacing below it, so it rounds to a smaller value. -/
theorem abs_rne_div_lt {a f : ℝ} (ha : φ.IsRep a) (hn : (2 : ℝ) ^ emin φ ≤ |a|)
    (hf : 1 + 2 ^ (1 - (φ.p : ℤ)) ≤ f) : |φ.rne (a / f)| < |a| := by
  have hw := Fmt.two_zpow_pos (1 - (φ.p : ℤ))
  have hf0 : 1 < f := by linarith
  suffices key : ∀ b : ℝ, φ.IsRep b → 2 ^ emin φ ≤ b → φ.rne (b / f) < b ∧ 0 ≤ φ.rne (b / f) by
    rcases le_or_gt 0 a with h0 | h0
    · rw [abs_of_nonneg h0] at hn ⊢
      obtain ⟨h1, h2⟩ := key a ha hn
      rw [abs_of_nonneg h2]; exact h1
    · rw [abs_of_neg h0] at hn ⊢
      obtain ⟨h1, h2⟩ := key (-a) (Fmt.isRep_neg ha) hn
      rw [show a / f = -(-a / f) by ring, Fmt.rne_neg, abs_neg, abs_of_nonneg h2]; exact h1
  intro b hb hbn
  have hb0 : 0 < b := lt_of_lt_of_le (Fmt.two_zpow_pos _) hbn
  set e := Int.log 2 b with hedef
  have he1 : (2 : ℝ) ^ e ≤ b := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hb0; exact_mod_cast this
  have he2 : b < 2 ^ (e + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) b; exact_mod_cast this
  have hemin : emin φ ≤ e := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hb0).mp (by exact_mod_cast hbn)
  have hq : φ.qmin ≤ e + 1 - φ.p := by rw [qmin_eq]; omega
  obtain ⟨k, hk⟩ := isRep_mul_ulp hb (by rwa [abs_of_pos hb0]) hq
  set u : ℝ := 2 ^ (e + 1 - φ.p) with hudef
  have hu : 0 < u := Fmt.two_zpow_pos _
  have hP : (2 : ℝ) ^ (e + 1) = 2 ^ φ.p * u := by
    rw [hudef, ← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring
  have hPe : (2 : ℝ) ^ e * 2 = 2 ^ φ.p * u := by rw [← hP, zpow_add_one₀ (by norm_num)]
  have hwP : (2 : ℝ) ^ (1 - (φ.p : ℤ)) * 2 ^ φ.p = 2 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; norm_num
  have h4 := Fmt.two_pow_p_ge (φ := φ)
  -- `b - u` is in the format
  have hs : φ.IsRep (b - u) := by
    have hk1 : (1 : ℝ) ≤ k := by
      have : (0 : ℝ) < k := by
        by_contra h; push Not at h; nlinarith
      have : (0 : ℤ) < k := by exact_mod_cast this
      exact_mod_cast this
    have hk2 : (k : ℝ) < 2 ^ φ.p := by
      by_contra h; push Not at h; nlinarith
    refine ⟨k - 1, e + 1 - φ.p, ?_, hq, by rw [hk]; push_cast; ring⟩
    have : (0 : ℝ) ≤ k - 1 := by linarith
    have h1 : (0 : ℤ) ≤ k - 1 := by exact_mod_cast this
    have h2 : ((k - 1 : ℤ) : ℝ) ≤ 2 ^ φ.p := by push_cast; linarith
    rw [abs_of_nonneg h1]; exact_mod_cast h2
  -- the quotient is more than half a spacing below `b`
  have hδ : u / 2 < b - b / f := by
    have hfb : b - b / f = b * (f - 1) / f := by field_simp
    rw [hfb, lt_div_iff₀ (by linarith)]
    -- `2 b (f - 1) ≥ 2 ^ p u (f - 1) > u f`
    have hbe : 2 ^ φ.p * u ≤ 2 * b := by linarith
    have hf1 : 0 ≤ f - 1 := by linarith
    have key : f < 2 ^ φ.p * (f - 1) := by nlinarith
    nlinarith
  have hne : φ.rne (b / f) ≠ b := by
    intro h
    have hn := Fmt.rne_nearest (b / f) hs
    rw [h] at hn
    have hle : b / f ≤ b := div_le_self hb0.le hf0.le
    rw [abs_of_nonpos (by linarith : b / f - b ≤ 0)] at hn
    rcases abs_cases (b / f - (b - u)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at hn <;> linarith
  have hle : φ.rne (b / f) ≤ b := Fmt.rne_le_of_le hb (div_le_self hb0.le hf0.le)
  have hge : 0 ≤ φ.rne (b / f) :=
    Fmt.le_rne_of_le Fmt.isRep_zero (div_nonneg hb0.le (by linarith))
  exact ⟨lt_of_le_of_ne hle hne, hge⟩


theorem isRep_g : φ.IsRep (1 + 2 ^ (1 - (φ.p : ℤ))) := by
  have hp := φ.hp
  have h1 : (2 : ℝ) ^ (1 - (φ.p : ℤ)) * 2 ^ (φ.p - 1) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    push_cast [Nat.cast_sub (by omega : 1 ≤ φ.p)]; norm_num
  refine ⟨2 ^ (φ.p - 1) + 1, 1 - φ.p, ?_, ?_, ?_⟩
  · have : (2 : ℤ) ^ φ.p = 2 * 2 ^ (φ.p - 1) := by rw [← pow_succ']; congr 1; omega
    have : (1 : ℤ) ≤ 2 ^ (φ.p - 1) := one_le_pow₀ (by norm_num)
    rw [abs_of_pos (by omega)]; omega
  · have := φ.hemax; unfold Fmt.qmin; omega
  · push_cast; rw [add_mul, mul_comm, h1, one_mul, add_comm]

/-- For a normal bound in the format, a row above the bound gets a factor at least
`1 + 2^(1-p)`: its norm is at least one spacing above the bound, so their ratio exceeds
`1 + 2^-p`, which rounds up to at least `1 + 2^(1-p)`. -/
theorem factor_ge (C : Clamp φ) (hbR : φ.IsRep C.bound) (hbn : (2 : ℝ) ^ emin φ ≤ C.bound)
    {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) (ha : C.above r) :
    1 + 2 ^ (1 - (φ.p : ℤ)) ≤ C.factor r := by
  have hc := C.cur_ok hr
  set c := C.cur r with hcdef
  set B := C.bound with hBdef
  have hcB : B < c := ha
  have hB0 : 0 < B := lt_of_lt_of_le (Fmt.two_zpow_pos _) hbn
  set e := Int.log 2 B
  have he1 : (2 : ℝ) ^ e ≤ B := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hB0; exact_mod_cast this
  have he2 : B < 2 ^ (e + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) B; exact_mod_cast this
  have hemin : emin φ ≤ e := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) hB0).mp (by exact_mod_cast hbn)
  have hq : φ.qmin ≤ e + 1 - φ.p := by rw [qmin_eq]; omega
  obtain ⟨kb, hkb⟩ := isRep_mul_ulp hbR (by rwa [abs_of_pos hB0]) hq
  obtain ⟨kc, hkc⟩ := isRep_mul_ulp hc.1.1 (by rw [abs_of_pos (by linarith)]; linarith) hq
  set u : ℝ := 2 ^ (e + 1 - φ.p) with hudef
  have hu : 0 < u := Fmt.two_zpow_pos _
  -- `c ≥ B + u`
  have hstep : B + u ≤ c := by
    have : (kb : ℝ) < kc := by
      by_contra h; push Not at h; nlinarith
    have : kb < kc := by exact_mod_cast this
    have : (kb : ℝ) + 1 ≤ kc := by exact_mod_cast this
    rw [hkb, hkc]; nlinarith
  -- `u / B > 2 ^ -p`
  have hP : (2 : ℝ) ^ (e + 1) * 2 ^ (-(φ.p : ℤ)) = u := by
    rw [hudef, ← zpow_add₀ (by norm_num)]; congr 1
  have hp0 := Fmt.two_zpow_pos (-(φ.p : ℤ))
  set q := c / B with hqdef
  have hq1 : 1 + 2 ^ (-(φ.p : ℤ)) < q := by
    rw [hqdef, lt_div_iff₀ hB0]; nlinarith
  have hw2 : (2 : ℝ) ^ (1 - (φ.p : ℤ)) = 2 * 2 ^ (-(φ.p : ℤ)) := by
    rw [show (1 : ℤ) - φ.p = -(φ.p : ℤ) + 1 by ring, zpow_add_one₀ (by norm_num)]; ring
  set g : ℝ := 1 + 2 ^ (1 - (φ.p : ℤ)) with hgdef
  -- `rne q ≥ g`
  have hrq : g ≤ φ.rne q := by
    rcases le_or_gt g q with hgq | hgq
    · exact Fmt.le_rne_of_le isRep_g hgq
    by_contra hlt
    push Not at hlt
    have h1 : 1 ≤ φ.rne q := Fmt.le_rne_of_le isRep_one (by linarith)
    -- the format has no value strictly between `1` and `g`
    obtain ⟨k, hk⟩ := isRep_mul_ulp (e := 0) (Fmt.rne_isRep (φ := φ) q)
      (by rw [zpow_zero, abs_of_pos (by linarith)]; exact h1)
      (by have := φ.hemax; unfold Fmt.qmin; omega)
    have hp := φ.hp
    have hone : (2 : ℝ) ^ (0 + 1 - (φ.p : ℤ)) * ((2 ^ (φ.p - 1) : ℤ) : ℝ) = 1 := by
      push_cast; rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      push_cast [Nat.cast_sub (by omega : 1 ≤ φ.p)]; norm_num
    have hz : (0 : ℤ) + 1 - φ.p = 1 - φ.p := by ring
    rw [hz] at hk hone
    have hk1 : ((2 ^ (φ.p - 1) : ℤ) : ℝ) ≤ k := by
      by_contra h; push Not at h
      have := mul_lt_mul_of_pos_left h (Fmt.two_zpow_pos (1 - (φ.p : ℤ)))
      nlinarith
    have hk2 : (k : ℝ) < ((2 ^ (φ.p - 1) : ℤ) : ℝ) + 1 := by
      by_contra h; push Not at h
      have := mul_le_mul_of_nonneg_left h (Fmt.two_zpow_pos (1 - (φ.p : ℤ))).le
      nlinarith
    have hk1' : 2 ^ (φ.p - 1) ≤ k := by exact_mod_cast hk1
    have hk2' : k < 2 ^ (φ.p - 1) + 1 := by exact_mod_cast hk2
    have hkeq : k = 2 ^ (φ.p - 1) := by omega
    have hr1 : φ.rne q = 1 := by rw [hk, hkeq]; linarith
    have hn := Fmt.rne_nearest q (isRep_g (φ := φ))
    rw [hr1, abs_of_pos (by linarith), abs_of_neg (by linarith)] at hn
    linarith
  -- the factor
  have hgM : g ≤ φ.maxFinite := by
    have := two_pow_emax_le (φ := φ)
    have h2 : (2 : ℝ) ≤ 2 ^ φ.emax := by
      have := φ.hemax
      calc (2 : ℝ) = 2 ^ (1 : ℤ) := by norm_num
        _ ≤ 2 ^ φ.emax := zpow_le_zpow_right₀ (by norm_num) this
    have : (2 : ℝ) ^ (1 - (φ.p : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by have := φ.hp; omega)
    linarith
  have hnt : g ≤ nanToNum φ (F64.div φ c B) := by
    simp only [F64.div, F64.round]
    split_ifs with h
    · exact hrq
    · have : ¬ (c / B < 0) := not_lt.mpr (div_nonneg (by linarith) hB0.le)
      simp only [this, decide_false, nanToNum]; exact hgM
  exact hnt.trans (le_max_left _ _)

/-- Sums of at most `2 ^ p` values in `[0, B]`, with `k B` in the format for `k ≤ 2 ^ p`, stay
finite and below `#leaves · B`. -/
theorem eval_le {xs : List F64} {B : ℝ} (hB0 : 0 ≤ B)
    (hx : ∀ v ∈ xs, ∃ w, v = fin w ∧ 0 ≤ w ∧ w ≤ B)
    (hBrep : ∀ k : ℕ, k ≤ 2 ^ φ.p → Ok φ (k * B)) (t : STree) (ht : t.leaves.length ≤ 2 ^ φ.p) :
    ∃ w, t.eval φ xs = fin w ∧ 0 ≤ w ∧ w ≤ t.leaves.length * B := by
  induction t with
  | leaf i =>
    simp only [STree.eval, STree.leaves, List.length_singleton, Nat.cast_one, one_mul,
      List.getD_eq_getElem?_getD]
    cases hi : xs[i]? with
    | none => exact ⟨0, rfl, le_rfl, hB0⟩
    | some v => simpa using hx v (List.mem_of_getElem? hi)
  | node l r ihl ihr =>
    simp only [STree.leaves, List.length_append] at ht ⊢
    obtain ⟨wl, hl, hl0, hl1⟩ := ihl (by omega)
    obtain ⟨wr, hr, hr0, hr1⟩ := ihr (by omega)
    have hK := hBrep (l.leaves.length + r.leaves.length) ht
    push_cast at hK
    have habs : |wl + wr| ≤ (l.leaves.length + r.leaves.length) * B := by
      rw [abs_of_nonneg (by linarith)]; linarith
    obtain ⟨h1, _, h3⟩ := round_of_abs_le hK habs
    simp only [STree.eval, hl, hr, F64.add, h1]
    refine ⟨_, rfl, Fmt.rne_zero (φ := φ) ▸ Fmt.rne_mono (by linarith), ?_⟩
    push_cast
    exact (le_abs_self _).trans h3


/-- `k · 2^emin` is a finite value of the format for `k ≤ 2 ^ p`. -/
theorem ok_mul_emin (hφ : φ.p + 1 < φ.emax) (k : ℕ) (hk : k ≤ 2 ^ φ.p) :
    Ok φ (k * 2 ^ emin φ) := by
  refine ⟨?_, ?_⟩
  · have := Fmt.isRep_of_mul (φ := φ) (k := (k : ℤ)) (e := emin φ)
      (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hk)
      (by rw [qmin_eq]; have := φ.hp; omega)
    rwa [Int.cast_natCast] at this
  · have h1 : (k : ℝ) ≤ 2 ^ φ.p := by exact_mod_cast hk
    have h2 : (2 : ℝ) ^ φ.p * 2 ^ emin φ ≤ 2 ^ φ.emax := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
      exact zpow_le_zpow_right₀ (by norm_num) (by unfold emin; omega)
    rw [abs_of_nonneg (by positivity)]
    calc (k : ℝ) * 2 ^ emin φ ≤ 2 ^ φ.p * 2 ^ emin φ :=
          mul_le_mul_of_nonneg_right h1 (Fmt.two_zpow_pos _).le
      _ ≤ _ := h2.trans two_pow_emax_le

/-- A row of subnormal values is within any bound when `p = 2` (the squares round to zero), and
within a bound at least `d · 2^emin` when `p = 1`. -/
theorem not_above_of_subnormal (C : Clamp φ) (hφ : φ.p + 1 < φ.emax) (hb0 : 0 ≤ C.bound)
    {r : List ℝ} (hL1 : C.ord = .l1 → (r.length : ℝ) * 2 ^ emin φ ≤ C.bound ∧ r.length ≤ 2 ^ φ.p)
    (hs : ∀ a ∈ r, |a| < 2 ^ emin φ) : ¬ C.above r := by
  unfold Clamp.above Clamp.cur
  rw [not_lt]
  cases ho : C.ord with
  | l2 =>
    have hsq : ∀ v ∈ (r.map fin).map (F64.sq φ), v = fin 0 := by
      simp only [List.map_map, List.mem_map]
      rintro _ ⟨a, ha, rfl⟩
      simp only [Function.comp, F64.sq]
      apply round_eq _ (by simp; exact Fmt.maxFinite_pos.le)
      apply rne_tiny
      have h1 := hs a ha
      have h0 := abs_nonneg a
      have : |a * a| < 2 ^ emin φ * 2 ^ emin φ := by rw [abs_mul]; nlinarith
      have h2 : (2 : ℝ) ^ emin φ * 2 ^ emin φ ≤ 2 ^ φ.qmin / 2 := by
        rw [← zpow_add₀ (by norm_num), div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ (by norm_num)]
        exact zpow_le_zpow_right₀ (by norm_num) (by unfold emin Fmt.qmin; omega)
      linarith
    simp only [rowNorm, reduce_zeros C.P _ hsq]
    simp only [F64.sqrt, lt_irrefl, ite_false, Real.sqrt_zero, round_of_ok ok_zero, nanToNum]
    exact hb0
  | l1 =>
    obtain ⟨hlen, hlenp⟩ := hL1 ho
    simp only [rowNorm, List.map_map]
    by_cases hne : r = []
    · subst hne; simp only [List.map_nil, reduce, ite_true, nanToNum]; exact hb0
    unfold reduce
    rw [ite_eq_right (by simpa using hne), List.length_map]
    have hlen' := (C.P.perm r.length (List.length_pos_iff.mpr hne)).length_eq
    rw [List.length_range] at hlen'
    obtain ⟨w, hw, _, hw1⟩ := eval_le (φ := φ) (B := 2 ^ emin φ) (Fmt.two_zpow_pos _).le
      (xs := r.map (F64.abs ∘ fin))
      (by simp only [List.mem_map]
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨|a|, rfl, abs_nonneg _, (hs a ha).le⟩)
      (ok_mul_emin hφ) _ (by rw [hlen']; exact hlenp)
    rw [hw, nanToNum]
    rw [hlen'] at hw1
    linarith

/-- The magnitude of a value, in units of the smallest subnormal. -/
noncomputable def mag (φ : Fmt) (a : ℝ) : ℕ := ⌊|a| / 2 ^ φ.qmin⌋₊

theorem mag_le {a b : ℝ} (h : |a| ≤ |b|) : mag φ a ≤ mag φ b :=
  Nat.floor_mono (div_le_div_of_nonneg_right h (Fmt.two_zpow_pos _).le)

theorem mag_lt {a b : ℝ} (ha : φ.IsRep a) (hb : φ.IsRep b) (h : |a| < |b|) : mag φ a < mag φ b := by
  obtain ⟨j, rfl⟩ := Fmt.isRep_mul_qmin ha
  obtain ⟨k, rfl⟩ := Fmt.isRep_mul_qmin hb
  have ht := Fmt.two_zpow_pos φ.qmin
  have e : ∀ i : ℤ, |(i : ℝ) * 2 ^ φ.qmin| / 2 ^ φ.qmin = |(i : ℝ)| := by
    intro i; rw [abs_mul, abs_of_pos ht]; field_simp
  have hjk : |(j : ℝ)| < |(k : ℝ)| := by
    rw [abs_mul, abs_mul, abs_of_pos ht] at h
    exact lt_of_mul_lt_mul_right h ht.le
  have hjk' : |j| < |k| := by
    have : ((|j| : ℤ) : ℝ) < ((|k| : ℤ) : ℝ) := by push_cast; exact hjk
    exact_mod_cast this
  have h1 : |(j : ℝ)| + 1 ≤ |(k : ℝ)| := by
    have : |j| + 1 ≤ |k| := hjk'
    have : ((|j| + 1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at this; exact this
  unfold mag
  rw [e, e]
  calc ⌊|(j : ℝ)|⌋₊ < ⌊|(j : ℝ)|⌋₊ + 1 := Nat.lt_succ_self _
    _ = ⌊|(j : ℝ)| + 1⌋₊ := (Nat.floor_add_one (abs_nonneg _)).symm
    _ ≤ ⌊|(k : ℝ)|⌋₊ := Nat.floor_mono h1

/-- The total magnitude of the rows: the loop's termination measure. -/
noncomputable def measure (φ : Fmt) (rows : List (List ℝ)) : ℕ :=
  (rows.map fun r => (r.map (mag φ)).sum).sum

theorem rowMag_body_le (C : Clamp φ) {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a) :
    ((C.body r).map (mag φ)).sum ≤ (r.map (mag φ)).sum := by
  simp only [Clamp.body, List.map_map]
  apply List.sum_le_sum
  intro a ha
  obtain ⟨h1, _, h3⟩ := C.div_factor (hr a ha) r
  simp only [Function.comp, h1, toR]
  exact mag_le h3

/-- The hypotheses of termination: `norm` is a normal float, and for `p = 1` at least `d` times the
smallest normal float, for `d ≤ 2 ^ p` columns. -/
structure TermHyp (C : Clamp φ) : Prop where
  fmt : φ.p + 1 < φ.emax
  rep : φ.IsRep C.bound
  normal : (2 : ℝ) ^ emin φ ≤ C.bound
  l1 : C.ord = .l1 → (C.origin.length : ℝ) * 2 ^ emin φ ≤ C.bound ∧ C.origin.length ≤ 2 ^ φ.p

theorem TermHyp.l1_row {C : Clamp φ} (H : TermHyp C) {r : List ℝ} (hlen : r.length ≤ C.origin.length) :
    C.ord = .l1 → (r.length : ℝ) * 2 ^ emin φ ≤ C.bound ∧ r.length ≤ 2 ^ φ.p := by
  intro ho
  obtain ⟨h1, h2⟩ := H.l1 ho
  refine ⟨le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (Fmt.two_zpow_pos _).le) h1,
    by omega⟩

theorem rowMag_body_lt {C : Clamp φ} (H : TermHyp C) {r : List ℝ} (hr : ∀ a ∈ r, Ok φ a)
    (hlen : r.length ≤ C.origin.length) (ha : C.above r) :
    ((C.body r).map (mag φ)).sum < (r.map (mag φ)).sum := by
  have hb0 : 0 ≤ C.bound := le_trans (Fmt.two_zpow_pos _).le H.normal
  obtain ⟨a, ha', hn⟩ : ∃ a ∈ r, 2 ^ emin φ ≤ |a| := by
    by_contra h
    push Not at h
    exact not_above_of_subnormal C H.fmt hb0 (H.l1_row hlen) h ha
  simp only [Clamp.body, List.map_map]
  apply List.sum_lt_sum
  · intro b hb
    obtain ⟨h1, _, h3⟩ := C.div_factor (hr b hb) r
    simp only [Function.comp, h1, toR]
    exact mag_le h3
  · refine ⟨a, ha', ?_⟩
    obtain ⟨h1, h2, _⟩ := C.div_factor (hr a ha') r
    simp only [Function.comp, h1, toR]
    exact mag_lt h2.1 (hr a ha').1
      (abs_rne_div_lt (hr a ha').1 hn (factor_ge C H.rep H.normal hr ha))

theorem loop_terminates {C : Clamp φ} (H : TermHyp C) :
    ∀ m (rows : List (List ℝ)), (∀ r ∈ rows, (∀ a ∈ r, Ok φ a) ∧ r.length ≤ C.origin.length) →
      measure φ rows ≤ m → ∃ out, C.loop m rows = some out := by
  intro m
  induction m with
  | zero =>
    intro rows hinv hm
    have hab : ¬ ∃ r ∈ rows, C.above r := by
      rintro ⟨r, hr, ha⟩
      have := rowMag_body_lt H (hinv r hr).1 (hinv r hr).2 ha
      have : 0 < measure φ rows := by
        unfold measure
        exact lt_of_lt_of_le (Nat.zero_lt_of_lt this) (List.le_sum_of_mem (List.mem_map.mpr ⟨r, hr, rfl⟩))
      omega
    exact ⟨rows, by simp [Clamp.loop, hab]⟩
  | succ m ih =>
    intro rows hinv hm
    by_cases hab : ∃ r ∈ rows, C.above r
    · have hlt : measure φ (rows.map C.body) < measure φ rows := by
        unfold measure
        rw [List.map_map]
        obtain ⟨r, hr, ha⟩ := hab
        apply List.sum_lt_sum
        · intro s hs; exact rowMag_body_le C (hinv s hs).1
        · exact ⟨r, hr, rowMag_body_lt H (hinv r hr).1 (hinv r hr).2 ha⟩
      have hinv' : ∀ r ∈ rows.map C.body, (∀ a ∈ r, Ok φ a) ∧ r.length ≤ C.origin.length := by
        simp only [List.mem_map]
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨C.body_ok (hinv r hr).1, by simp only [Clamp.body, List.length_map]; exact (hinv r hr).2⟩
      obtain ⟨out, hout⟩ := ih _ hinv' (by omega)
      exact ⟨out, by simp only [Clamp.loop, hab, ite_true, hout]⟩
    · exact ⟨rows, by simp only [Clamp.loop, hab, ite_false]⟩

/-- **Termination.** When `norm` is a normal float, and for `p = 1` at least `d · 2^emin` with
`d ≤ 2^p` columns (`d` the length of `origin`), `_function` returns on every non-empty dataset.
`nonterm_subnormal` and `nonterm_normal` show that neither condition can be dropped. -/
theorem clamp_terminates {C : Clamp φ} (H : TermHyp C) (x : List (List F64)) :
    ∃ n out, C.clamp n x = .ok out := by
  obtain ⟨out, hout⟩ := loop_terminates H _ (x.map C.pre) (by
    simp only [List.mem_map]
    rintro _ ⟨row, _, rfl⟩
    exact ⟨C.pre_ok row, by simp only [Clamp.pre, List.length_zipWith]; omega⟩) le_rfl
  exact ⟨measure φ (x.map C.pre), out.map C.post, by simp only [Clamp.clamp, hout]⟩

end Termination


/-! ## The fixed code -/

section Fixed

variable {φ : Fmt}

theorem zipWith_subR_self (os : List ℝ) :
    List.zipWith (F64.subR φ) (os.map fin) os = os.map fun _ => fin 0 := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, ih, F64.subR, sub_self, round_of_ok ok_zero]

namespace Clamp

variable (C : Clamp φ)

/-- **The norm check (F9, F12, F16).** Every output row passes the output domain's norm check,
for any origin: rows that rounding leaves outside the ball are replaced by `origin`, which is at
norm 0 from itself. -/
theorem clamp_member (hb : 0 ≤ C.bound) {n : ℕ} {x out : List (List F64)}
    (h : C.clamp n x = .ok out) : ∀ row ∈ out, C.memberNorm row := by
  unfold clamp at h
  split at h
  · cases h
    simp only [List.mem_map]
    rintro _ ⟨r, _, rfl⟩
    unfold post
    split_ifs with ho
    · unfold memberNorm outside
      rw [zipWith_subR_self, rowNorm_zeros C.P C.ord _ (by simp)]
      simp only [F64.gt, not_lt]; exact hb
    · exact ho
  · cases h

/-- **The empty dataset (F13)** is clamped to the empty dataset. -/
theorem clamp_empty (n : ℕ) : C.clamp n [] = .ok [] := by
  cases n <;> simp [clamp, loop]

end Clamp

/-- The hypotheses of termination follow from a lower bound `2^(emin + p)` on `norm`, which
`make_np_clamp`'s minimum norm (`2^-458` for `f64`, `2^-39` for `f32`) exceeds. -/
theorem TermHyp.of_min {C : Clamp φ} (hφ : φ.p + 1 < φ.emax) (hrep : φ.IsRep C.bound)
    (hmin : (2 : ℝ) ^ (emin φ + φ.p) ≤ C.bound) (hd : C.origin.length ≤ 2 ^ φ.p) : TermHyp C := by
  have h2 : (2 : ℝ) ^ (emin φ + φ.p) = 2 ^ φ.p * 2 ^ emin φ := by
    rw [zpow_add₀ (by norm_num), zpow_natCast, mul_comm]
  refine ⟨hφ, hrep, le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega)) hmin, fun _ => ⟨?_, hd⟩⟩
  calc (C.origin.length : ℝ) * 2 ^ emin φ ≤ 2 ^ φ.p * 2 ^ emin φ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (Fmt.two_zpow_pos _).le
    _ = _ := h2.symm
    _ ≤ _ := hmin

/-! ### True norms (F10)

The loop bounds the norms numpy computes. The true norms exceed them by rounding errors: a
relative error `u = 2^-p` per operation, and, for `p = 2`, an absolute error `η = 2^qmin / 2` per
square that underflows. -/

/-- The rounding error is at most `2^-p` relative, plus half the smallest subnormal. -/
theorem rne_err (z : ℝ) : |φ.rne z - z| ≤ 2 ^ (-(φ.p : ℤ)) * |z| + 2 ^ φ.qmin / 2 := by
  have hp := Fmt.two_zpow_pos (-(φ.p : ℤ))
  have hη := Fmt.two_zpow_pos φ.qmin
  rcases eq_or_ne z 0 with h0 | h0
  · rw [h0, Fmt.rne_zero]; simp only [sub_zero, abs_zero, mul_zero, zero_add]; positivity
  have hq := Fmt.two_zpow_pos (φ.fexp z)
  have herr : |φ.rne z - z| ≤ 2 ^ φ.fexp z / 2 := by
    have key : φ.rne z - z =
        -((z / 2 ^ φ.fexp z - roundEven (z / 2 ^ φ.fexp z)) * 2 ^ φ.fexp z) := by
      unfold Fmt.rne; field_simp; ring
    rw [key, abs_neg, abs_mul, abs_of_pos hq]
    have := roundEven_half (z / 2 ^ φ.fexp z)
    nlinarith
  by_cases hn : φ.qmin ≤ Int.log 2 |z| - φ.p + 1
  · have hf : φ.fexp z = Int.log 2 |z| - φ.p + 1 := max_eq_left hn
    have hlog : (2 : ℝ) ^ Int.log 2 |z| ≤ |z| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr h0)
    have : (2 : ℝ) ^ φ.fexp z / 2 = 2 ^ Int.log 2 |z| * 2 ^ (-(φ.p : ℤ)) := by
      rw [hf, ← zpow_add₀ (by norm_num), div_eq_iff (by norm_num), ← zpow_add_one₀ (by norm_num)]
      ring_nf
    rw [this] at herr
    nlinarith
  · have hf : φ.fexp z = φ.qmin := max_eq_right (by unfold Fmt.fexp at *; omega)
    rw [hf] at herr
    nlinarith [abs_nonneg z]

theorem round_eq_fin {x c : ℝ} (h : F64.round φ x = fin c) : c = φ.rne x := by
  unfold F64.round at h
  split_ifs at h
  cases h; rfl

/-- A summation tree with an infinite leaf sums to infinity. -/
theorem eval_inf {xs : List F64} (hx : ∀ v ∈ xs, NN φ v) {i : ℕ}
    (hi : xs.getD i (fin 0) = inf false) (t : STree) (ht : i ∈ t.leaves) :
    t.eval φ xs = inf false := by
  induction t with
  | leaf j =>
    simp only [STree.leaves, List.mem_singleton] at ht
    subst ht; exact hi
  | node l r ihl ihr =>
    simp only [STree.leaves, List.mem_append] at ht
    have hl := eval_nn hx l
    have hr := eval_nn hx r
    simp only [STree.eval]
    rcases ht with ht | ht
    · rw [ihl ht]
      generalize r.eval φ xs = v at hr
      match v with
      | fin _ => rfl
      | inf b => simp only [NN] at hr; subst hr; simp [F64.add]
      | nan => exact hr.elim
    · rw [ihr ht]
      generalize l.eval φ xs = v at hl
      match v with
      | fin _ => rfl
      | inf b => simp only [NN] at hl; subst hl; simp [F64.add]
      | nan => exact hl.elim

theorem getD_nn {xs : List F64} (hx : ∀ v ∈ xs, NN φ v) (i : ℕ) : NN φ (xs.getD i (fin 0)) := by
  simp only [List.getD_eq_getElem?_getD]
  cases hi : xs[i]? with
  | none => exact ⟨ok_zero, le_rfl⟩
  | some v => exact hx v (List.mem_of_getElem? hi)

/-- A summation tree loses at most a relative `2^-p` per addition: its leaves sum to at most
`c / (1 - 2^-p)^(#leaves - 1)`. -/
theorem eval_lower {xs : List F64} (hx : ∀ v ∈ xs, NN φ v) (t : STree) {c : ℝ}
    (h : t.eval φ xs = fin c) :
    (t.leaves.map fun i => nanToNum φ (xs.getD i (fin 0))).sum
      * (1 - 2 ^ (-(φ.p : ℤ))) ^ (t.leaves.length - 1) ≤ c := by
  have hu : (2 : ℝ) ^ (-(φ.p : ℤ)) ≤ 1 / 4 := by
    have := Fmt.two_pow_p_ge (φ := φ)
    rw [zpow_neg, zpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hu0 := Fmt.two_zpow_pos (-(φ.p : ℤ))
  set W := 1 - (2 : ℝ) ^ (-(φ.p : ℤ)) with hW
  have hW0 : 0 ≤ W := by linarith
  have hW1 : W ≤ 1 := by linarith
  have hsum0 : ∀ t : STree, 0 ≤ (t.leaves.map fun i => nanToNum φ (xs.getD i (fin 0))).sum := by
    intro t
    apply List.sum_nonneg
    simp only [List.mem_map]
    rintro _ ⟨i, _, rfl⟩
    exact (nanToNum_nn (getD_nn hx i)).2
  induction t generalizing c with
  | leaf i =>
    simp only [STree.eval] at h
    simp only [STree.leaves, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.length_singleton, Nat.sub_self, pow_zero, mul_one, h, nanToNum, le_refl]
  | node l r ihl ihr =>
    have hl := eval_nn hx l
    have hr := eval_nn hx r
    simp only [STree.eval] at h
    -- both sides are finite
    obtain ⟨cl, hcl⟩ : ∃ cl, l.eval φ xs = fin cl := by
      generalize l.eval φ xs = v at hl h
      match v with
      | fin a => exact ⟨a, rfl⟩
      | inf b =>
        simp only [NN] at hl; subst hl
        generalize r.eval φ xs = w at hr h
        match w with
        | fin _ => simp [F64.add] at h
        | inf b' => simp only [NN] at hr; subst hr; simp [F64.add] at h
        | nan => exact hr.elim
      | nan => exact hl.elim
    obtain ⟨cr, hcr⟩ : ∃ cr, r.eval φ xs = fin cr := by
      generalize r.eval φ xs = v at hr h
      match v with
      | fin a => exact ⟨a, rfl⟩
      | inf b =>
        simp only [NN] at hr; subst hr
        rw [hcl] at h; simp [F64.add] at h
      | nan => exact hr.elim
    simp only [hcl, hcr] at h hl hr
    simp only [F64.add] at h
    have hc := round_eq_fin h
    have hadd := Fmt.rne_add_err (φ := φ) hl.1.1 hr.1.1
    have hz : 0 ≤ cl + cr := add_nonneg hl.2 hr.2
    rw [abs_of_nonneg hz] at hadd
    have hcge : (cl + cr) * W ≤ c := by
      rw [hc, hW]; have := (abs_le.mp hadd).1; nlinarith
    have hl1 := ihl hcl
    have hr1 := ihr hcr
    have hnl := leaves_length_pos l
    have hnr := leaves_length_pos r
    simp only [STree.leaves, List.map_append, List.sum_append, List.length_append]
    set Sl := (l.leaves.map fun i => nanToNum φ (xs.getD i (fin 0))).sum
    set Sr := (r.leaves.map fun i => nanToNum φ (xs.getD i (fin 0))).sum
    have hSl := hsum0 l
    have hSr := hsum0 r
    have e1 : W ^ (l.leaves.length + r.leaves.length - 1) ≤ W ^ (l.leaves.length - 1) * W := by
      rw [← pow_succ]; exact pow_le_pow_of_le_one hW0 hW1 (by omega)
    have e2 : W ^ (l.leaves.length + r.leaves.length - 1) ≤ W ^ (r.leaves.length - 1) * W := by
      rw [← pow_succ]; exact pow_le_pow_of_le_one hW0 hW1 (by omega)
    calc (Sl + Sr) * W ^ (l.leaves.length + r.leaves.length - 1)
        = Sl * W ^ (l.leaves.length + r.leaves.length - 1)
          + Sr * W ^ (l.leaves.length + r.leaves.length - 1) := by ring
      _ ≤ Sl * (W ^ (l.leaves.length - 1) * W) + Sr * (W ^ (r.leaves.length - 1) * W) := by
          gcongr
      _ ≤ cl * W + cr * W := by
          have := mul_le_mul_of_nonneg_right hl1 hW0
          have := mul_le_mul_of_nonneg_right hr1 hW0
          nlinarith
      _ ≤ c := by linarith


theorem sum_range_getD' (f : F64 → ℝ) (xs : List F64) :
    ((List.range xs.length).map fun i => f (xs.getD i (fin 0))).sum = (xs.map f).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

/-- `add.reduce` loses at most a relative `2^-p` per addition. -/
theorem reduce_lower {P : Plan} {xs : List F64} (hx : ∀ v ∈ xs, NN φ v) {c : ℝ}
    (h : reduce φ P xs = fin c) :
    (xs.map (nanToNum φ)).sum * (1 - 2 ^ (-(φ.p : ℤ))) ^ (xs.length - 1) ≤ c := by
  unfold reduce at h
  split_ifs at h with hne
  · cases h; subst hne; simp
  · have hperm := P.perm xs.length (List.length_pos_iff.mpr hne)
    have := eval_lower hx _ h
    rwa [(hperm.map _).sum_eq, hperm.length_eq, List.length_range, sum_range_getD'] at this

/-- When `add.reduce` is finite, so is every element. -/
theorem reduce_fin {P : Plan} {xs : List F64} (hx : ∀ v ∈ xs, NN φ v) {c : ℝ}
    (h : reduce φ P xs = fin c) : ∀ v ∈ xs, ∃ a, v = fin a := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hnn := hx _ hv
  match hxi : xs[i] with
  | fin a => exact ⟨a, rfl⟩
  | nan => rw [hxi] at hnn; exact hnn.elim
  | inf b =>
    exfalso
    rw [hxi] at hnn
    simp only [NN] at hnn
    subst hnn
    have hne : xs ≠ [] := List.ne_nil_of_mem hv
    unfold reduce at h
    simp only [hne, ite_false] at h
    have hperm := P.perm xs.length (List.length_pos_iff.mpr hne)
    have hmem : i ∈ (P.tree xs.length).leaves := hperm.symm.subset (List.mem_range.mpr hi)
    have hgd : xs.getD i (fin 0) = inf false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hxi]
    rw [eval_inf hx hgd _ hmem] at h
    cases h

/-- **True L1 norms.** A row whose computed L1 norm is `c` has true L1 norm at most
`c / (1 - 2^-p)^(n - 1)`. -/
theorem l1_true_norm (P : Plan) {w : List ℝ} (hw : ∀ a ∈ w, Ok φ a) {c : ℝ}
    (h : rowNorm φ P .l1 (w.map fin) = fin c) :
    (w.map fun a => |a|).sum * (1 - 2 ^ (-(φ.p : ℤ))) ^ (w.length - 1) ≤ c := by
  simp only [rowNorm] at h
  have hx : ∀ v ∈ (w.map fin).map F64.abs, NN φ v := by
    simp only [List.map_map, List.mem_map]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨isRep_abs (hw a ha).1, by rw [abs_abs]; exact (hw a ha).2⟩, abs_nonneg a⟩
  have := reduce_lower hx h
  simp only [List.map_map, List.length_map] at this
  exact this

theorem sum_affine (w : List ℝ) (W η : ℝ) :
    (w.map fun a => a ^ 2 * W - η).sum = (w.map fun a => a ^ 2).sum * W - w.length * η := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- **True L2 norms (F10).** A row whose computed L2 norm is `c` has true squared norm at most
`((c + η)² + n η) / (1 - 2^-p)^(n + 2)`, with `η = 2^qmin / 2`: each square loses at most a
relative `2^-p` and an absolute `η` (when it underflows), each addition and the square root a
relative `2^-p`. -/
theorem l2_true_norm (P : Plan) {w : List ℝ} (hw : ∀ a ∈ w, Ok φ a) {c : ℝ}
    (h : rowNorm φ P .l2 (w.map fin) = fin c) :
    (w.map fun a => a ^ 2).sum * (1 - 2 ^ (-(φ.p : ℤ))) ^ (w.length + 2)
      ≤ (c + 2 ^ φ.qmin / 2) ^ 2 + w.length * (2 ^ φ.qmin / 2) := by
  have hu : (2 : ℝ) ^ (-(φ.p : ℤ)) ≤ 1 / 4 := by
    have := Fmt.two_pow_p_ge (φ := φ)
    rw [zpow_neg, zpow_natCast, inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hu0 := Fmt.two_zpow_pos (-(φ.p : ℤ))
  have hη0 : (0 : ℝ) < 2 ^ φ.qmin / 2 := by have := Fmt.two_zpow_pos φ.qmin; linarith
  set u := (2 : ℝ) ^ (-(φ.p : ℤ)) with hudef
  set η := (2 : ℝ) ^ φ.qmin / 2 with hηdef
  set W := 1 - u with hW
  have hW0 : 0 ≤ W := by linarith
  have hW1 : W ≤ 1 := by linarith
  have hx : ∀ v ∈ (w.map fin).map (F64.sq φ), NN φ v := by
    simp only [List.map_map, List.mem_map]
    rintro _ ⟨a, _, rfl⟩
    exact round_nn (mul_self_nonneg a)
  simp only [rowNorm] at h
  generalize hR : reduce φ P ((w.map fin).map (F64.sq φ)) = R at h
  have hRnn : NN φ R := hR ▸ reduce_nn hx
  obtain ⟨s, rfl⟩ : ∃ s, R = fin s := by
    match R, hRnn, h with
    | fin s, _, _ => exact ⟨s, rfl⟩
    | inf b, hb, h => simp only [NN] at hb; subst hb; simp [F64.sqrt] at h
    | nan, hb, _ => exact hb.elim
  have hs0 : 0 ≤ s := hRnn.2
  simp only [F64.sqrt, show ¬ s < 0 from not_lt.mpr hs0, ite_false] at h
  have hc := round_eq_fin h
  have hsq := Real.sqrt_nonneg s
  have hc1 : W * Real.sqrt s ≤ c + η := by
    have := (abs_le.mp (rne_err (φ := φ) (Real.sqrt s))).1
    rw [abs_of_nonneg hsq, ← hc] at this
    rw [hW]; nlinarith
  have hc0 : 0 ≤ c := by rw [hc]; exact Fmt.rne_zero (φ := φ) ▸ Fmt.rne_mono hsq
  have hcs : W ^ 2 * s ≤ (c + η) ^ 2 := by
    have e : W ^ 2 * s = (W * Real.sqrt s) ^ 2 := by rw [mul_pow, Real.sq_sqrt hs0]
    rw [e]; exact pow_le_pow_left₀ (by positivity) hc1 2
  by_cases hw0 : w = []
  · subst hw0
    simp only [List.map_nil, List.sum_nil, zero_mul, List.length_nil, Nat.cast_zero, add_zero]
    positivity
  have hn : 1 ≤ w.length := List.length_pos_iff.mpr hw0
  have hfin := reduce_fin hx hR
  have hl : ∀ a ∈ w, a ^ 2 * W - η ≤ nanToNum φ (F64.sq φ (fin a)) := by
    intro a ha
    obtain ⟨l, hl⟩ := hfin _ (List.mem_map.mpr ⟨fin a, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩)
    have hle := (abs_le.mp (rne_err (φ := φ) (a * a))).1
    rw [abs_of_nonneg (mul_self_nonneg a)] at hle
    simp only [F64.sq] at hl ⊢
    rw [hl, nanToNum, round_eq_fin hl, hW]
    nlinarith
  have hL := reduce_lower hx hR
  simp only [List.length_map] at hL
  have hsumL : (w.map fun a => a ^ 2 * W - η).sum
      ≤ (((w.map fin).map (F64.sq φ)).map (nanToNum φ)).sum := by
    simp only [List.map_map]
    exact List.sum_le_sum hl
  rw [sum_affine] at hsumL
  set A := (w.map fun a => a ^ 2).sum
  set L := (((w.map fin).map (F64.sq φ)).map (nanToNum φ)).sum
  set n := w.length
  have e1 : W ^ (n + 1) = W ^ (n - 1) * W ^ 2 := by rw [← pow_add]; congr 1; omega
  have hp1 := pow_nonneg hW0 (n + 1)
  have hp1' : W ^ (n + 1) ≤ 1 := pow_le_one₀ hW0 hW1
  have step : (A * W - n * η) * W ^ (n + 1) ≤ (c + η) ^ 2 := by
    calc (A * W - n * η) * W ^ (n + 1) ≤ L * W ^ (n + 1) := mul_le_mul_of_nonneg_right hsumL hp1
      _ = L * W ^ (n - 1) * W ^ 2 := by rw [e1]; ring
      _ ≤ s * W ^ 2 := mul_le_mul_of_nonneg_right hL (by positivity)
      _ ≤ (c + η) ^ 2 := by linarith
  have hnη : (0 : ℝ) ≤ n * η := by positivity
  calc A * W ^ (n + 2) = A * W * W ^ (n + 1) := by ring
    _ ≤ (c + η) ^ 2 + n * η * W ^ (n + 1) := by nlinarith
    _ ≤ (c + η) ^ 2 + n * η := by nlinarith


namespace Clamp

variable (C : Clamp φ)

/-- **True norms of the outputs (F10), with origin zero.** Every output row is a row `w` of
finite floats whose true norm is within rounding error of the bound: for `p = 1`,
`‖w‖₁ (1 - 2^-p)^(n-1) ≤ norm`, and for `p = 2`,
`‖w‖₂² (1 - 2^-p)^(n+2) ≤ (norm + η)² + n η` with `η = 2^qmin / 2`. With `norm` at least
`make_np_clamp`'s minimum, `n η ≤ (2^-p norm)²` and `η ≤ 2^-p norm` for `n ≤ 2^p`, so
the underflow terms are at most a relative rounding error (`slack_le`). -/
theorem clamp_true_norm {d : ℕ} (hO : C.origin = List.replicate d 0) (hb : 0 ≤ C.bound)
    {n : ℕ} {x out : List (List F64)} (h : C.clamp n x = .ok out) :
    ∀ row ∈ out, ∃ w : List ℝ, row = w.map fin ∧
      (C.ord = .l1 → (w.map fun a => |a|).sum * (1 - 2 ^ (-(φ.p : ℤ))) ^ (w.length - 1)
        ≤ C.bound) ∧
      (C.ord = .l2 → (w.map fun a => a ^ 2).sum * (1 - 2 ^ (-(φ.p : ℤ))) ^ (w.length + 2)
        ≤ (C.bound + 2 ^ φ.qmin / 2) ^ 2 + w.length * (2 ^ φ.qmin / 2)) := by
  intro row hrow
  have hmem := C.clamp_member hb h row hrow
  obtain ⟨w, rfl, hw, hlen⟩ :
      ∃ w : List ℝ, row = w.map fin ∧ (∀ a ∈ w, Ok φ a) ∧ w.length ≤ d := by
    unfold clamp at h
    split at h
    · rename_i rows hl
      cases h
      obtain ⟨N, rfl, _⟩ := C.loop_spec hl
      simp only [List.mem_map] at hrow
      obtain ⟨_, ⟨_, ⟨row0, _, rfl⟩, rfl⟩, rfl⟩ := hrow
      have hok := C.iterate_ok (C.pre_ok row0) N
      have hlen : (C.body^[N] (C.pre row0)).length ≤ d := by
        have : ∀ M (s : List ℝ), (C.body^[M] s).length = s.length := by
          intro M; induction M with
          | zero => intro s; rfl
          | succ M ih => intro s; rw [Function.iterate_succ_apply, ih]; simp [body]
        rw [this, pre, List.length_zipWith, hO, List.length_replicate]; omega
      set s := C.body^[N] (C.pre row0)
      have hpost : C.postV0 s = s.map fin := by
        rw [postV0, hO, zipWith_zeros _ hlen]
        apply List.map_congr_left
        intro a ha; simp only [add_zero]; exact round_of_ok (hok a ha)
      unfold post
      split_ifs
      · refine ⟨List.replicate d 0, by rw [hO], ?_, by simp⟩
        intro a ha; rw [List.eq_of_mem_replicate ha]; exact ok_zero
      · exact ⟨s, hpost, hok, hlen⟩
    · cases h
  have hsub : List.zipWith (F64.subR φ) (w.map fin) C.origin = w.map fin := by
    rw [hO, zipWith_zeros _ (by simpa using hlen), List.map_map]
    apply List.map_congr_left
    intro a ha; simp only [Function.comp, F64.subR, sub_zero]; exact round_of_ok (hw a ha)
  unfold memberNorm outside at hmem
  rw [hsub] at hmem
  have hnn := rowNorm_nn (φ := φ) (P := C.P) (o := C.ord) hw
  obtain ⟨c, hc, hcb, hc0⟩ : ∃ c, rowNorm φ C.P C.ord (w.map fin) = fin c ∧ c ≤ C.bound ∧ 0 ≤ c := by
    generalize rowNorm φ C.P C.ord (w.map fin) = v at hmem hnn
    match v with
    | fin c => exact ⟨c, rfl, not_lt.mp hmem, hnn.2⟩
    | inf b => simp only [NN] at hnn; subst hnn; simp [F64.gt] at hmem
    | nan => exact hnn.elim
  refine ⟨w, rfl, fun ho => ?_, fun ho => ?_⟩
  · rw [ho] at hc; exact (l1_true_norm C.P hw hc).trans hcb
  · rw [ho] at hc
    have hη : (0 : ℝ) ≤ 2 ^ φ.qmin / 2 := by have := Fmt.two_zpow_pos φ.qmin; linarith
    have := l2_true_norm C.P hw hc
    have : (c + 2 ^ φ.qmin / 2) ^ 2 ≤ (C.bound + 2 ^ φ.qmin / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    linarith

end Clamp

/-- With `n η ≤ (u B)²` and `η ≤ u B`, the bound of `clamp_true_norm` for `p = 2` is
`B² ((1 + u)² + u²)`: a relative excess of about `(n / 2 + 2) u` on the norm. -/
theorem slack_le {B u η n : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η) (h1 : n * η ≤ (u * B) ^ 2)
    (h2 : η ≤ u * B) : (B + η) ^ 2 + n * η ≤ B ^ 2 * ((1 + u) ^ 2 + u ^ 2) := by
  have : (B + η) ^ 2 ≤ (B + u * B) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  nlinarith


theorem q32 : binary32.qmin = -149 := by decide

/-- The minimum norm `2^-458` of `make_np_clamp` for `f64` meets the hypotheses of
`TermHyp.of_min` and `slack_le`, for rows of at most `2^53` values. -/
theorem min_norm_f64 {B : ℝ} (hB : 2 ^ (-458 : ℤ) ≤ B) {n : ℕ} (hn : n ≤ 2 ^ 53) :
    (2 : ℝ) ^ (emin binary64 + binary64.p) ≤ B ∧
      (n : ℝ) * (2 ^ binary64.qmin / 2) ≤ (2 ^ (-(binary64.p : ℤ)) * B) ^ 2 ∧
      2 ^ binary64.qmin / 2 ≤ 2 ^ (-(binary64.p : ℤ)) * B := by
  set_option exponentiation.threshold 2200 in
  have he : emin binary64 + binary64.p = -969 := by decide
  rw [he, q64, p64]
  have hn' : (n : ℝ) ≤ 2 ^ 53 := by exact_mod_cast hn
  have hm : (2 : ℝ) ^ (-(53 : ℤ)) * 2 ^ (-458 : ℤ) ≤ 2 ^ (-(53 : ℤ)) * B :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hsq := pow_le_pow_left₀ (by positivity) hm 2
  refine ⟨le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hB, ?_, ?_⟩
  · calc (n : ℝ) * (2 ^ (-1074 : ℤ) / 2) ≤ 2 ^ 53 * (2 ^ (-1074 : ℤ) / 2) :=
          mul_le_mul_of_nonneg_right hn' (by positivity)
      _ = (2 ^ (-(53 : ℤ)) * 2 ^ (-458 : ℤ)) ^ 2 := by norm_num
      _ ≤ _ := hsq
  · calc (2 : ℝ) ^ (-1074 : ℤ) / 2 ≤ 2 ^ (-(53 : ℤ)) * 2 ^ (-458 : ℤ) := by norm_num
      _ ≤ _ := hm

/-- The same for the minimum norm `2^-39` for `f32`, for rows of at most `2^24` values. -/
theorem min_norm_f32 {B : ℝ} (hB : 2 ^ (-39 : ℤ) ≤ B) {n : ℕ} (hn : n ≤ 2 ^ 24) :
    (2 : ℝ) ^ (emin binary32 + binary32.p) ≤ B ∧
      (n : ℝ) * (2 ^ binary32.qmin / 2) ≤ (2 ^ (-(binary32.p : ℤ)) * B) ^ 2 ∧
      2 ^ binary32.qmin / 2 ≤ 2 ^ (-(binary32.p : ℤ)) * B := by
  have he : emin binary32 + binary32.p = -102 := by decide
  rw [he, q32, show binary32.p = 24 from rfl]
  have hn' : (n : ℝ) ≤ 2 ^ 24 := by exact_mod_cast hn
  have hm : (2 : ℝ) ^ (-(24 : ℤ)) * 2 ^ (-39 : ℤ) ≤ 2 ^ (-(24 : ℤ)) * B :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hsq := pow_le_pow_left₀ (by positivity) hm 2
  refine ⟨le_trans (zpow_le_zpow_right₀ (by norm_num) (by norm_num)) hB, ?_, ?_⟩
  · calc (n : ℝ) * (2 ^ (-149 : ℤ) / 2) ≤ 2 ^ 24 * (2 ^ (-149 : ℤ) / 2) :=
          mul_le_mul_of_nonneg_right hn' (by positivity)
      _ = (2 ^ (-(24 : ℤ)) * 2 ^ (-39 : ℤ)) ^ 2 := by norm_num
      _ ≤ _ := hsq
  · calc (2 : ℝ) ^ (-149 : ℤ) / 2 ≤ 2 ^ (-(24 : ℤ)) * 2 ^ (-39 : ℤ) := by norm_num
      _ ≤ _ := hm

end Fixed

end OpenDP.NpClamp
