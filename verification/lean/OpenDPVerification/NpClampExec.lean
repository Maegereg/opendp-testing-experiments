/-
An executable copy of the `make_np_clamp` model (`NpClamp.lean`), and numpy's summation order.

The model in `NpClamp.lean` computes over `ℝ`, so it cannot be run. This file defines the same
functions over `ℚ` (every float is a rational), and proves that each one agrees with the model:
`EF.toF` maps an executable float to the model's `F64`, and `clamp_toRes` states that running
`ClampQ.clamp` and mapping the result is the model's `Clamp.clamp`. Running it on an input therefore
evaluates the model on that input, and `verification/conformance/test_np_clamp.py` compares the
results with numpy and with `make_np_clamp` (`NpClampOracle.lean` is the entry point).

The model takes numpy's summation order as a parameter (`Plan`). `numpyPlan` is numpy's pairwise
summation (`pairwise_sum` in `numpy/_core/src/umath/loops_utils.h.src`): rows shorter than 8 are
summed left to right, rows up to 128 with 8 interleaved accumulators, and longer rows are split
in two at a multiple of 8. `numpyPlan` is a `Plan` (its leaves are a permutation of the row), so
all theorems about `Clamp` hold for it; that it is numpy's order is checked by the tests.
-/
import OpenDPVerification.NpClamp

namespace OpenDP.NpClamp.Exec

open OpenDP.Float OpenDP.NpClamp

/-! ## Rounding over `ℚ` -/

/-- `roundEven` over `ℚ`. -/
def roundEvenQ (y : ℚ) : ℤ :=
  if y - ⌊y⌋ < 1 / 2 then ⌊y⌋
  else if 1 / 2 < y - ⌊y⌋ then ⌊y⌋ + 1
  else if Even ⌊y⌋ then ⌊y⌋ else ⌊y⌋ + 1

theorem roundEven_cast (y : ℚ) : roundEven (y : ℝ) = roundEvenQ y := by
  have e : (y : ℝ) - (⌊y⌋ : ℝ) = ((y - ⌊y⌋ : ℚ) : ℝ) := by push_cast; rfl
  have half : (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; rfl
  have h1 : ((y : ℝ) - (⌊y⌋ : ℝ) < 1 / 2) ↔ (y - ⌊y⌋ < 1 / 2) := by
    rw [e, half, Rat.cast_lt]
  have h2 : (1 / 2 < (y : ℝ) - (⌊y⌋ : ℝ)) ↔ (1 / 2 < y - ⌊y⌋) := by
    rw [e, half, Rat.cast_lt]
  unfold roundEven roundEvenQ
  rw [Rat.floor_cast]
  simp only [h1, h2]

theorem log_cast (q : ℚ) : Int.log 2 (q : ℝ) = Int.log 2 q := by
  rcases le_or_gt q 0 with hq | hq
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast hq
    rw [Int.log_of_right_le_one _ (by linarith), Int.log_of_right_le_one _ (by linarith),
      Nat.ceil_eq_zero.mpr (inv_nonpos.mpr hq), Nat.ceil_eq_zero.mpr (inv_nonpos.mpr hq')]
  · have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hb : 1 < 2 := by norm_num
    apply le_antisymm
    · set k := Int.log 2 (q : ℝ)
      rw [← Int.zpow_le_iff_le_log hb hq]
      have h := Int.zpow_log_le_self hb hq'
      have : (((2 : ℚ) ^ k : ℚ) : ℝ) ≤ (q : ℝ) := by push_cast at h ⊢; exact h
      push_cast; exact Rat.cast_le.mp this
    · set k := Int.log 2 q
      rw [← Int.zpow_le_iff_le_log hb hq']
      have h := Int.zpow_log_le_self hb hq
      have : (((2 : ℚ) ^ k : ℚ) : ℝ) ≤ (q : ℝ) := Rat.cast_le.mpr (by push_cast at h ⊢; exact h)
      push_cast at this ⊢; exact this

/-- `Fmt.fexp` over `ℚ`. -/
def fexpQ (φ : Fmt) (x : ℚ) : ℤ := max (Int.log 2 |x| - φ.p + 1) φ.qmin

/-- `Fmt.rne` over `ℚ`. -/
def rneQ (φ : Fmt) (x : ℚ) : ℚ := roundEvenQ (x / 2 ^ fexpQ φ x) * (2 : ℚ) ^ fexpQ φ x

theorem fexp_cast (φ : Fmt) (x : ℚ) : φ.fexp (x : ℝ) = fexpQ φ x := by
  unfold Fmt.fexp fexpQ
  rw [← Rat.cast_abs, log_cast]

theorem rne_cast (φ : Fmt) (x : ℚ) : φ.rne (x : ℝ) = (rneQ φ x : ℝ) := by
  unfold Fmt.rne rneQ
  rw [fexp_cast]
  have : (x : ℝ) / 2 ^ fexpQ φ x = ((x / 2 ^ fexpQ φ x : ℚ) : ℝ) := by push_cast; rfl
  rw [this, roundEven_cast]
  push_cast; rfl

/-- `Fmt.maxFinite` over `ℚ`. -/
def maxFiniteQ (φ : Fmt) : ℚ := (2 ^ φ.p - 1) * 2 ^ φ.qtop

theorem maxFinite_cast (φ : Fmt) : φ.maxFinite = (maxFiniteQ φ : ℝ) := by
  unfold Fmt.maxFinite maxFiniteQ; push_cast; rfl

/-! ## Square roots

`rne (√a)` for a rational `a`: the exponent of `√a` is half that of `a`, and the integer nearest
to `√t` is found from `Nat.sqrt ⌊t⌋` and a comparison of `t` with `(k + 1/2)²`. -/

theorem log_sqrt {a : ℝ} (ha : 0 ≤ a) : Int.log 2 (Real.sqrt a) = Int.log 2 a / 2 := by
  rcases ha.eq_or_lt with rfl | ha
  · simp
  have hb : 1 < 2 := by norm_num
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  set m := Int.log 2 a
  have hm1 : (2 : ℝ) ^ m ≤ a := by exact_mod_cast Int.zpow_log_le_self hb ha
  have hm2 : a < (2 : ℝ) ^ (m + 1) := by exact_mod_cast Int.lt_zpow_succ_log_self hb a
  have hk1 : 2 * (m / 2) ≤ m := by omega
  have hk2 : m + 1 ≤ 2 * (m / 2 + 1) := by omega
  have two : (1 : ℝ) ≤ 2 := by norm_num
  apply le_antisymm
  · have : Real.sqrt a < (2 : ℝ) ^ (m / 2 + 1) := by
      rw [Real.sqrt_lt' (zpow_pos (by norm_num) _), ← zpow_natCast, ← zpow_mul]
      calc a < (2 : ℝ) ^ (m + 1) := hm2
        _ ≤ (2 : ℝ) ^ ((m / 2 + 1) * ((2 : ℕ) : ℤ)) := zpow_le_zpow_right₀ two (by push_cast; linarith)
    have := (Int.lt_zpow_iff_log_lt hb hs).mp (by exact_mod_cast this)
    omega
  · rw [← Int.zpow_le_iff_le_log hb hs]
    push_cast
    rw [Real.le_sqrt (zpow_nonneg (by norm_num) _) ha.le, ← zpow_natCast, ← zpow_mul]
    calc (2 : ℝ) ^ (m / 2 * ((2 : ℕ) : ℤ)) ≤ (2 : ℝ) ^ m := zpow_le_zpow_right₀ two (by push_cast; linarith)
      _ ≤ a := hm1

/-- The integer nearest to `√t`, ties to even. -/
def roundEvenSqrtQ (t : ℚ) : ℤ :=
  let k : ℤ := ((Nat.sqrt ⌊t⌋₊ : ℕ) : ℤ)
  if t < (k + 1 / 2) ^ 2 then k
  else if (k + 1 / 2) ^ 2 < t then k + 1
  else if Even k then k else k + 1

theorem roundEven_sqrt_cast {t : ℚ} (ht : 0 ≤ t) :
    roundEven (Real.sqrt t) = roundEvenSqrtQ t := by
  set n := ⌊t⌋₊
  set k : ℤ := ((Nat.sqrt n : ℕ) : ℤ)
  have hn1 : (n : ℚ) ≤ t := Nat.floor_le ht
  have hn2 : t < n + 1 := Nat.lt_floor_add_one t
  have hk1 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hk2 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
  have hk1' : (k : ℚ) ^ 2 ≤ t := by
    have : ((Nat.sqrt n * Nat.sqrt n : ℕ) : ℚ) ≤ n := by exact_mod_cast hk1
    simp only [k]; push_cast at this ⊢; nlinarith
  have hk2' : t < ((k : ℚ) + 1) ^ 2 := by
    have : (n : ℚ) + 1 ≤ ((Nat.sqrt n + 1) * (Nat.sqrt n + 1) : ℕ) := by exact_mod_cast hk2
    simp only [k]; push_cast at this ⊢; nlinarith
  have hk0 : (0 : ℝ) ≤ k := by simp only [k]; positivity
  have hfl : ⌊Real.sqrt t⌋ = k := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [Real.le_sqrt hk0 (by exact_mod_cast ht)]; exact_mod_cast hk1'
    · rw [Real.sqrt_lt' (by linarith)]; exact_mod_cast hk2'
  have e : ((k : ℝ) + 1 / 2) ^ 2 = ((((k : ℚ) + 1 / 2) ^ 2 : ℚ) : ℝ) := by push_cast; rfl
  have h1 : (Real.sqrt t - k < 1 / 2) ↔ (t < (k + 1 / 2) ^ 2) := by
    rw [sub_lt_iff_lt_add', Real.sqrt_lt' (by linarith), e, Rat.cast_lt]
  have h2 : (1 / 2 < Real.sqrt t - k) ↔ ((k + 1 / 2) ^ 2 < t) := by
    rw [lt_sub_iff_add_lt', Real.lt_sqrt (by linarith), e, Rat.cast_lt]
  unfold roundEven roundEvenSqrtQ
  rw [hfl]
  simp only [h1, h2]
  rfl

/-- `rne (√a)` for `0 ≤ a`. -/
def rneSqrtQ (φ : Fmt) (a : ℚ) : ℚ :=
  let e := max (Int.log 2 a / 2 - φ.p + 1) φ.qmin
  roundEvenSqrtQ (a / 2 ^ (2 * e)) * (2 : ℚ) ^ e

theorem rne_sqrt_cast (φ : Fmt) {a : ℚ} (ha : 0 ≤ a) :
    φ.rne (Real.sqrt a) = (rneSqrtQ φ a : ℝ) := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hfe : φ.fexp (Real.sqrt a) = max (Int.log 2 a / 2 - φ.p + 1) φ.qmin := by
    unfold Fmt.fexp
    rw [abs_of_nonneg (Real.sqrt_nonneg _), log_sqrt ha', log_cast]
  unfold Fmt.rne rneSqrtQ
  rw [hfe]
  set e := max (Int.log 2 a / 2 - φ.p + 1) φ.qmin
  have h2e : (0 : ℝ) < 2 ^ e := zpow_pos (by norm_num) _
  have hdiv : Real.sqrt a / 2 ^ e = Real.sqrt ((a / 2 ^ (2 * e) : ℚ) : ℝ) := by
    push_cast
    rw [Real.sqrt_div' _ (zpow_nonneg (by norm_num) _), mul_comm, zpow_mul,
      show ((2 : ℝ) ^ e) ^ (2 : ℤ) = ((2 : ℝ) ^ e) ^ (2 : ℕ) from zpow_natCast _ 2,
      Real.sqrt_sq h2e.le]
  rw [hdiv, roundEven_sqrt_cast (div_nonneg ha (zpow_nonneg (by norm_num) _))]
  push_cast; rfl

/-! ## Floats -/

/-- An executable `F64`. -/
inductive EF where
  | fin (x : ℚ)
  | inf (neg : Bool)
  | nan
  deriving Inhabited, DecidableEq, Repr

namespace EF

/-- The model's float. -/
noncomputable def toF : EF → F64
  | fin x => .fin x
  | inf s => .inf s
  | nan => .nan

@[simp] theorem toF_fin (x : ℚ) : (fin x).toF = .fin x := rfl
@[simp] theorem toF_inf (s : Bool) : (inf s).toF = .inf s := rfl
@[simp] theorem toF_nan : nan.toF = .nan := rfl

variable (φ : Fmt)

def round (x : ℚ) : EF :=
  if |rneQ φ x| ≤ maxFiniteQ φ then fin (rneQ φ x) else inf (decide (x < 0))

def add : EF → EF → EF
  | fin a, fin b => round φ (a + b)
  | inf s, fin _ => inf s
  | fin _, inf s => inf s
  | inf s, inf t => if s = t then inf s else nan
  | _, _ => nan

def subR (a : EF) (o : ℚ) : EF :=
  match a with
  | fin a => round φ (a - o)
  | inf s => inf s
  | nan => nan

def addR (a : EF) (o : ℚ) : EF :=
  match a with
  | fin a => round φ (a + o)
  | inf s => inf s
  | nan => nan

def abs : EF → EF
  | fin a => fin |a|
  | inf _ => inf false
  | nan => nan

def sq : EF → EF
  | fin a => round φ (a * a)
  | inf _ => inf false
  | nan => nan

def sqrt : EF → EF
  | fin a =>
    if a < 0 then nan
    else if |rneSqrtQ φ a| ≤ maxFiniteQ φ then fin (rneSqrtQ φ a) else inf false
  | inf false => inf false
  | inf true => nan
  | nan => nan

def div (a b : ℚ) : EF := round φ (a / b)

def nanToNum : EF → ℚ
  | fin a => a
  | inf false => maxFiniteQ φ
  | inf true => -maxFiniteQ φ
  | nan => 0

def gt : EF → ℚ → Bool
  | fin a, b => decide (b < a)
  | inf neg, _ => neg = false
  | nan, _ => false

def toR : EF → ℚ
  | fin a => a
  | _ => 0

/-! Each operation agrees with the model's. -/

theorem round_toF (x : ℚ) : (round φ x).toF = F64.round φ x := by
  unfold round F64.round
  rw [rne_cast, maxFinite_cast]
  have hc : (|(rneQ φ x : ℝ)| ≤ (maxFiniteQ φ : ℝ)) ↔ |rneQ φ x| ≤ maxFiniteQ φ := by
    constructor <;> intro h <;> exact_mod_cast h
  have hneg : decide ((x : ℝ) < 0) = decide (x < 0) := by simp
  simp only [hc, hneg]
  split_ifs <;> rfl

theorem add_toF (a b : EF) : (add φ a b).toF = F64.add φ a.toF b.toF := by
  cases a <;> cases b <;> simp only [add, F64.add, round_toF, toF_fin, toF_inf, toF_nan]
  all_goals first | (push_cast; rfl) | (split_ifs <;> rfl)

theorem subR_toF (a : EF) (o : ℚ) : (subR φ a o).toF = F64.subR φ a.toF o := by
  cases a <;> simp [subR, F64.subR, round_toF]

theorem addR_toF (a : EF) (o : ℚ) : (addR φ a o).toF = F64.addR φ a.toF o := by
  cases a <;> simp [addR, F64.addR, round_toF]

theorem abs_toF (a : EF) : (abs a).toF = F64.abs a.toF := by
  cases a <;> simp [abs, F64.abs]

theorem sq_toF (a : EF) : (sq φ a).toF = F64.sq φ a.toF := by
  cases a <;> simp [sq, F64.sq, round_toF]

theorem sqrt_toF (a : EF) : (sqrt φ a).toF = F64.sqrt φ a.toF := by
  cases a with
  | fin a =>
    simp only [sqrt, F64.sqrt, toF_fin]
    by_cases ha : a < 0
    · have : (a : ℝ) < 0 := by exact_mod_cast ha
      simp [ha, this]
    · have ha' : ¬ (a : ℝ) < 0 := by exact_mod_cast ha
      push Not at ha
      simp only [ha', ite_false, not_lt.mpr ha]
      unfold F64.round
      rw [rne_sqrt_cast φ ha, maxFinite_cast]
      have hc : (|(rneSqrtQ φ a : ℝ)| ≤ (maxFiniteQ φ : ℝ)) ↔ |rneSqrtQ φ a| ≤ maxFiniteQ φ := by
        constructor <;> intro h <;> exact_mod_cast h
      have hs : decide (Real.sqrt (a : ℝ) < 0) = false := by
        simp [not_lt.mpr (Real.sqrt_nonneg _)]
      simp only [hc, hs]
      split_ifs <;> rfl
  | inf s => cases s <;> rfl
  | nan => rfl

theorem div_toF (a b : ℚ) : (div φ a b).toF = F64.div φ a b := by
  simp [div, F64.div, round_toF]

theorem nanToNum_toF (a : EF) : F64.nanToNum φ a.toF = (nanToNum φ a : ℝ) := by
  rcases a with a | (_ | _) | _ <;> simp [nanToNum, F64.nanToNum, maxFinite_cast]

theorem gt_toF (a : EF) (b : ℚ) : F64.gt a.toF b ↔ gt a b = true := by
  rcases a with a | (_ | _) | _ <;> simp [gt, F64.gt]

theorem toR_toF (a : EF) : F64.toR a.toF = (toR a : ℝ) := by
  cases a <;> simp [toR, F64.toR]

end EF

/-! ## Summation -/

/-- `STree.eval` -/
def evalQ (φ : Fmt) (xs : List EF) : STree → EF
  | .leaf i => xs.getD i (.fin 0)
  | .node l r => EF.add φ (evalQ φ xs l) (evalQ φ xs r)

theorem evalQ_toF (φ : Fmt) (xs : List EF) (t : STree) :
    (evalQ φ xs t).toF = t.eval φ (xs.map EF.toF) := by
  induction t with
  | leaf i =>
    simp only [evalQ, STree.eval, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases xs[i]? <;> simp
  | node l r ihl ihr => simp [evalQ, STree.eval, EF.add_toF, ihl, ihr]

/-- `reduce` -/
def reduceQ (φ : Fmt) (P : Plan) (xs : List EF) : EF :=
  if xs.isEmpty then .fin 0 else evalQ φ xs (P.tree xs.length)

theorem reduceQ_toF (φ : Fmt) (P : Plan) (xs : List EF) :
    (reduceQ φ P xs).toF = reduce φ P (xs.map EF.toF) := by
  cases xs <;> simp [reduceQ, reduce, evalQ_toF]

/-- `rowNorm` -/
def rowNormQ (φ : Fmt) (P : Plan) (o : Ord) (row : List EF) : EF :=
  match o with
  | .l1 => reduceQ φ P (row.map EF.abs)
  | .l2 => EF.sqrt φ (reduceQ φ P (row.map (EF.sq φ)))

theorem rowNormQ_toF (φ : Fmt) (P : Plan) (o : Ord) (row : List EF) :
    (rowNormQ φ P o row).toF = rowNorm φ P o (row.map EF.toF) := by
  cases o
  · simp [rowNormQ, rowNorm, reduceQ_toF, Function.comp_def, EF.abs_toF]
  · simp [rowNormQ, rowNorm, EF.sqrt_toF, reduceQ_toF, Function.comp_def, EF.sq_toF]

/-! ## numpy's summation order -/

/-- Add the elements `l` to `t`, left to right. -/
def chain (t : STree) (l : List ℕ) : STree := l.foldl (fun t i => .node t (.leaf i)) t

theorem chain_leaves (t : STree) (l : List ℕ) : (chain t l).leaves = t.leaves ++ l := by
  induction l generalizing t with
  | nil => simp [chain]
  | cons i l ih =>
    simp only [chain, List.foldl_cons] at ih ⊢
    rw [ih]; simp [STree.leaves]

/-- An accumulator of a block: `r[j] = a[s]`, then `r[j] += a[s + 8]`, ... (`q` elements). -/
def acc (s q : ℕ) : STree := chain (.leaf s) (List.range' (s + 8) (q - 1) 8)

/-- `pairwise_sum` for `8 ≤ n ≤ 128`: 8 accumulators over the first `8 * (n / 8)` elements, combined
as `((r[0] + r[1]) + (r[2] + r[3])) + ((r[4] + r[5]) + (r[6] + r[7]))`, then the rest added
left to right. -/
def block (s n : ℕ) : STree :=
  let q := n / 8
  let r := fun j => acc (s + j) q
  chain (.node (.node (.node (r 0) (r 1)) (.node (r 2) (r 3)))
    (.node (.node (r 4) (r 5)) (.node (r 6) (r 7)))) (List.range' (s + 8 * q) (n % 8))

/-- numpy's `pairwise_sum` over the `n` elements starting at `s`. -/
def pairwise (s n : ℕ) : STree :=
  if n < 8 then chain (.leaf s) (List.range' (s + 1) (n - 1))
  else if n ≤ 128 then block s n
  else
    let n2 := n / 2 - n / 2 % 8
    .node (pairwise s n2) (pairwise (s + n2) (n - n2))
termination_by n
decreasing_by all_goals omega

theorem flatMap_cons_perm (l : List ℕ) (f : ℕ → ℕ) (g : ℕ → List ℕ) :
    (l.flatMap fun a => f a :: g a).Perm (l.map f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_cons, List.cons_append]
    refine List.Perm.cons _ ((ih.append_left (g a)).trans ?_)
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _

/-- The 8 accumulators together cover the block. -/
theorem interleave_perm (s q : ℕ) :
    ((List.range 8).flatMap fun j => List.range' (s + j) q 8).Perm (List.range' s (8 * q)) := by
  induction q generalizing s with
  | zero => simp
  | succ q ih =>
    have h1 : (fun j => List.range' (s + j) (q + 1) 8) =
        fun j => (s + j) :: List.range' (s + 8 + j) q 8 := by
      funext j; rw [List.range'_succ, Nat.add_right_comm]
    rw [h1]
    refine (flatMap_cons_perm _ _ _).trans ?_
    rw [← List.range'_eq_map_range, show 8 * (q + 1) = 8 + 8 * q by ring, ← List.range'_append]
    exact (ih (s + 8)).append_left _

theorem pairwise_perm (s n : ℕ) (hn : 0 < n) : (pairwise s n).leaves.Perm (List.range' s n) := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  rw [pairwise]
  split_ifs with h8 h128
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [chain_leaves, STree.leaves, List.range'_succ]
  · have hq : 0 < n / 8 := by omega
    have hacc : ∀ j, (acc (s + j) (n / 8)).leaves = List.range' (s + j) (n / 8) 8 := by
      intro j
      obtain ⟨m, hm⟩ : ∃ m, n / 8 = m + 1 := ⟨n / 8 - 1, by omega⟩
      simp [acc, chain_leaves, STree.leaves, hm, List.range'_succ]
    have hblk : (block s n).leaves = (List.range 8).flatMap (fun j => List.range' (s + j) (n / 8) 8)
        ++ List.range' (s + 8 * (n / 8)) (n % 8) := by
      simp only [block, chain_leaves, STree.leaves, hacc]
      simp [List.range_succ, List.flatMap]
    rw [hblk]
    have := (interleave_perm s (n / 8)).append_right (List.range' (s + 8 * (n / 8)) (n % 8))
    rw [List.range'_append_1, show 8 * (n / 8) + n % 8 = n by omega] at this
    simpa using this
  · simp only [STree.leaves]
    have h := (ih (n / 2 - n / 2 % 8) (by omega) s (by omega)).append
      (ih (n - (n / 2 - n / 2 % 8)) (by omega) (s + (n / 2 - n / 2 % 8)) (by omega))
    rw [List.range'_append_1] at h
    simpa [show n / 2 - n / 2 % 8 + (n - (n / 2 - n / 2 % 8)) = n by omega] using h

/-- numpy's summation order. -/
def numpyPlan : Plan where
  tree n := pairwise 0 n
  perm n hn := by simpa [List.range_eq_range'] using pairwise_perm 0 n hn

/-! ## `_function` -/

/-- The parameters of `Clamp`, over `ℚ`. -/
structure ClampQ where
  P : Plan
  ord : Ord
  bound : ℚ
  origin : List ℚ

namespace ClampQ

variable (φ : Fmt) (E : ClampQ)

/-- The model's parameters. -/
noncomputable def toC : Clamp φ := ⟨E.P, E.ord, E.bound, E.origin.map (↑)⟩

def cur (r : List ℚ) : ℚ := EF.nanToNum φ (rowNormQ φ E.P E.ord (r.map .fin))

def above (r : List ℚ) : Bool := decide (E.bound < E.cur φ r)

def factor (r : List ℚ) : ℚ := max (EF.nanToNum φ (EF.div φ (E.cur φ r) E.bound)) 1

def body (r : List ℚ) : List ℚ :=
  let f := E.factor φ r
  r.map fun a => EF.toR (EF.div φ a f)

def loop : ℕ → List (List ℚ) → Option (List (List ℚ))
  | 0, rows => if rows.any (E.above φ) then none else some rows
  | n + 1, rows => if rows.any (E.above φ) then loop n (rows.map (E.body φ)) else some rows

def pre (row : List EF) : List ℚ :=
  List.zipWith (fun a o => EF.nanToNum φ (EF.subR φ a o)) row E.origin

def postV0 (r : List ℚ) : List EF := List.zipWith (fun a o => EF.round φ (a + o)) r E.origin

def outside (row : List EF) : Bool :=
  (rowNormQ φ E.P E.ord (List.zipWith (EF.subR φ) row E.origin)).gt E.bound

def post (r : List ℚ) : List EF :=
  if E.outside φ (E.postV0 φ r) then E.origin.map .fin else E.postV0 φ r

inductive Res where
  | ok (out : List (List EF))
  | diverge

def clamp (n : ℕ) (x : List (List EF)) : Res :=
  match E.loop φ n (x.map (E.pre φ)) with
  | some rows => .ok (rows.map (E.post φ))
  | none => .diverge

/-- The model's result. -/
noncomputable def Res.toRes : Res → Clamp.Res
  | .ok out => .ok (out.map (·.map EF.toF))
  | .diverge => .diverge

/-! Each function agrees with the model's. -/

/-- A row of rationals as a row of reals. -/
noncomputable abbrev castL (r : List ℚ) : List ℝ := r.map (↑)

theorem cur_eq (r : List ℚ) : (E.toC φ).cur (castL r) = (E.cur φ r : ℝ) := by
  have : (castL r).map F64.fin = (r.map EF.fin).map EF.toF := by simp [Function.comp_def]
  simp only [Clamp.cur, cur, toC, this, ← rowNormQ_toF, EF.nanToNum_toF]

theorem above_iff (r : List ℚ) : (E.toC φ).above (castL r) ↔ E.above φ r = true := by
  simp only [Clamp.above, above, cur_eq, decide_eq_true_iff]
  exact Rat.cast_lt

theorem factor_eq (r : List ℚ) : (E.toC φ).factor (castL r) = (E.factor φ r : ℝ) := by
  simp only [Clamp.factor, factor, cur_eq]
  rw [show F64.div φ (E.cur φ r : ℝ) (E.toC φ).bound = (EF.div φ (E.cur φ r) E.bound).toF from
    (EF.div_toF φ _ _).symm, EF.nanToNum_toF]
  push_cast; rfl

theorem body_eq (r : List ℚ) : (E.toC φ).body (castL r) = castL (E.body φ r) := by
  simp only [Clamp.body, body, factor_eq, List.map_map, Function.comp_def]
  congr 1; funext a
  rw [← EF.div_toF, EF.toR_toF]

theorem loop_eq (n : ℕ) (rows : List (List ℚ)) :
    (E.toC φ).loop n (rows.map castL) = (E.loop φ n rows).map (·.map castL) := by
  have hex : ∀ rows : List (List ℚ),
      (∃ r ∈ rows.map castL, (E.toC φ).above r) ↔ rows.any (E.above φ) = true := by
    intro rows; simp [above_iff]
  induction n generalizing rows with
  | zero =>
    simp only [Clamp.loop, loop]
    by_cases h : rows.any (E.above φ) = true
    · simp only [(hex rows).mpr h, h, ↓reduceIte]; rfl
    · have h' : ¬ ∃ r ∈ rows.map castL, (E.toC φ).above r := fun h' => h ((hex rows).mp h')
      simp only [h', h, ↓reduceIte]; rfl
  | succ n ih =>
    simp only [Clamp.loop, loop]
    by_cases h : rows.any (E.above φ) = true
    · simp only [(hex rows).mpr h, h, ↓reduceIte]
      rw [← ih, List.map_map]
      congr 1; simp [Function.comp_def, body_eq]
    · have h' : ¬ ∃ r ∈ rows.map castL, (E.toC φ).above r := fun h' => h ((hex rows).mp h')
      simp only [h', h, ↓reduceIte]; rfl

theorem pre_eq (row : List EF) : (E.toC φ).pre (row.map EF.toF) = castL (E.pre φ row) := by
  simp only [Clamp.pre, pre, toC, castL, List.zipWith_map_left, List.zipWith_map_right,
    List.map_zipWith]
  congr 1; funext a o
  rw [← EF.subR_toF, EF.nanToNum_toF]

theorem postV0_eq (r : List ℚ) : (E.toC φ).postV0 (castL r) = (E.postV0 φ r).map EF.toF := by
  simp only [Clamp.postV0, postV0, toC, castL, List.zipWith_map_left, List.zipWith_map_right,
    List.map_zipWith]
  congr 1; funext a o
  rw [EF.round_toF]; push_cast; rfl

theorem outside_iff (row : List EF) :
    (E.toC φ).outside (row.map EF.toF) ↔ E.outside φ row = true := by
  have : List.zipWith (F64.subR φ) (row.map EF.toF) (E.toC φ).origin =
      (List.zipWith (EF.subR φ) row E.origin).map EF.toF := by
    simp only [toC, List.zipWith_map_left, List.zipWith_map_right, List.map_zipWith]
    congr 1; funext a o; rw [EF.subR_toF]
  simp only [Clamp.outside, outside, this, ← rowNormQ_toF]
  exact EF.gt_toF _ _

theorem post_eq (r : List ℚ) : (E.toC φ).post (castL r) = (E.post φ r).map EF.toF := by
  unfold Clamp.post post
  rw [postV0_eq]
  by_cases h : E.outside φ (E.postV0 φ r) = true
  · simp only [(E.outside_iff φ _).mpr h, h, ↓reduceIte]; simp [toC, Function.comp_def]
  · have h' : ¬ (E.toC φ).outside ((E.postV0 φ r).map EF.toF) := fun h' => h ((E.outside_iff φ _).mp h')
    simp only [h', h, Bool.false_eq_true, ↓reduceIte]

/-- **Running `clamp` evaluates the model**: on any input, it returns the model's result. -/
theorem clamp_toRes (n : ℕ) (x : List (List EF)) :
    (E.clamp φ n x).toRes = (E.toC φ).clamp n (x.map (·.map EF.toF)) := by
  have hx : (x.map (·.map EF.toF)).map (E.toC φ).pre = (x.map (E.pre φ)).map castL := by
    simp [Function.comp_def, pre_eq]
  simp only [Clamp.clamp, clamp, hx, loop_eq]
  cases E.loop φ n (x.map (E.pre φ)) with
  | none => rfl
  | some rows => simp [Res.toRes, Function.comp_def, post_eq]

end ClampQ

/-! ## The constructor

Not part of the model, which takes the bound and origin as given: the test harness uses these to
compute them from `make_np_clamp`'s arguments, as the constructor does. -/

/-- The largest float of the format at most `q ≥ 0`: `norm_T`. -/
def floorFloat (φ : Fmt) (q : ℚ) : ℚ :=
  if maxFiniteQ φ ≤ q then maxFiniteQ φ else ⌊q / 2 ^ fexpQ φ q⌋ * 2 ^ fexpQ φ q

end OpenDP.NpClamp.Exec
