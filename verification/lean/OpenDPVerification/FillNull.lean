/-
`make_expr_fill_null` (`rust/src/transformations/make_stable_expr/expr_fill_null/mod.rs`).

The constructor builds the Polars expression `data.fill_null(fill)`, which Polars evaluates later.
It claims:
* the output domain is the data's domain with bounds dropped and no nulls; its element type is the
  data's (the fill must have it), and it may hold NaN when the data or the fill may;
* the stability map `d_in ↦ d_in`.

## The model

Polars' `fill_null` is modelled per row (trusted, and checked by the conformance tests in
`expr_fill_null/test.rs`): a row's output is its data value, or its fill value if the data is null
(`fillRow`). The fill is another column of the same row (the constructor then requires a
row-by-row context), or a scalar repeated on every row. A column domain is a nullability flag and
a predicate on values (`ColDom`).

For F21, `clip` and `sum` are modelled on the floats of `NpClamp.lean`: `clip` keeps NaN, and
`sum` adds along a summation tree (any `Plan`). The noise mechanism adds noise to each value after
rounding it to a rational, which maps NaN to 0 (`discretize_vec` in
`rust/src/measurements/noise/nature/float/mod.rs`): this is `F64.nanToNum`.

## Results

* `fill_member`: the output is in the claimed domain when every fill value satisfies the data's
  predicate (with bounds dropped). `fill_nan_counterexample` (F20): otherwise it can fail; a NaN
  fill on a column whose domain excludes NaN.
* `fill_member_fixed` (the fix of F20): with the output's NaN flag the data's or the fill's, the
  output is always in the claimed domain; `fill_noNaN_fixed`: if that domain excludes NaN, no output
  value is NaN, so the F21 query is rejected by `sum`, which requires data without NaN.
* `fill_stable`: `d_out ≤ d_in` under the symmetric distance, for a column fill (a row function)
  and for a scalar fill (a function of each data value).
* `null_leak` (F21): `fill_nan(0).fill_null(NaN).clip(0, 1).sum()` gives `n` on `n` rows of `1.0`,
  and `0` once a null row is added, at symmetric distance 1, for every summation order. The noise is
  added to these values, while the sum's stability map allows a difference of 1.
* F19 (the output type is the supertype of the data's and the fill's) is not modelled; it, and its
  fix (the fill must have the data's type), are checked by running (`expr_fill_null/test.rs`).
-/
import OpenDPVerification.NpClamp

namespace OpenDP.FillNull

open OpenDP.Float OpenDP.NpClamp OpenDP.NpClamp.F64

/-! ## Model -/

/-- `fill_null` on one row: the data value, or the fill value if the data is null. -/
def fillRow {α : Type*} (d : Option α) (f : α) : α := d.getD f

/-- A column domain: whether nulls are allowed, and a predicate on values (the element domain:
its NaN flag, and bounds). -/
structure ColDom (α : Type*) where
  nullable : Bool
  P : α → Prop

/-- Membership of a column of nullable values. -/
def ColDom.Mem {α : Type*} (D : ColDom α) (col : List (Option α)) : Prop :=
  ∀ c ∈ col, match c with
    | none => D.nullable = true
    | some v => D.P v

/-- Membership of a column without nulls. -/
def ColDom.MemV {α : Type*} (D : ColDom α) (col : List α) : Prop :=
  D.Mem (col.map some)

/-! ## The output domain -/

/-- **The output domain.** The column `fill_null` returns is in the claimed domain (no nulls, the
predicate `P` the data's predicate keeps after dropping bounds) when each data value and each fill
value satisfies `P`. `rows` pairs each row's data value with its fill value: the fill column's, or
the scalar. -/
theorem fill_member {α : Type*} (Dd : ColDom α) (P : α → Prop) (hP : ∀ v, Dd.P v → P v)
    (rows : List (Option α × α)) (hd : Dd.Mem (rows.map Prod.fst))
    (hf : ∀ r ∈ rows, P r.2) :
    (ColDom.MemV ⟨false, P⟩ (rows.map fun r => fillRow r.1 r.2)) := by
  intro c hc
  simp only [List.map_map, List.mem_map, Function.comp_apply] at hc
  obtain ⟨⟨d, f⟩, hr, rfl⟩ := hc
  cases d with
  | none => exact hf _ hr
  | some v => exact hP v (hd (some v) (List.mem_map.mpr ⟨_, hr, rfl⟩))

/-- A float column domain that excludes NaN (the claimed output domain when the data excludes NaN:
the constructor keeps the data's NaN flag). -/
def noNaN : ColDom F64 := ⟨false, fun v => v ≠ nan⟩

/-- **F20.** Filling the nulls of a column whose domain excludes NaN with NaN gives NaN, which the
claimed output domain excludes. The fill's domain (a NaN literal, or a column that may hold NaN)
is not consulted. -/
theorem fill_nan_counterexample :
    ColDom.Mem ⟨true, fun v => v ≠ nan⟩ [none] ∧
      ¬ noNaN.MemV ([((none : Option F64), nan)].map fun r => fillRow r.1 r.2) := by
  refine ⟨by simp [ColDom.Mem], ?_⟩
  simp [ColDom.MemV, ColDom.Mem, noNaN, fillRow]

/-- A float column domain without bounds and nulls, allowing NaN when `b` (the NaN flag). -/
def nanDom (b : Bool) : ColDom F64 := ⟨false, fun v => b = true ∨ v ≠ nan⟩

/-- **The fixed output domain (F20).** The output may hold NaN when the data or the fill may: the
NaN flag of the output domain is the data's or the fill's. With this flag, the output is in the
claimed domain (and the fill's type is the data's, F19, so the fill values are floats of the same
format). -/
theorem fill_member_fixed (nd nf : Bool) (rows : List (Option F64 × F64))
    (hd : ColDom.Mem ⟨true, fun v => nd = true ∨ v ≠ nan⟩ (rows.map Prod.fst))
    (hf : ∀ r ∈ rows, nf = true ∨ r.2 ≠ nan) :
    (nanDom (nd || nf)).MemV (rows.map fun r => fillRow r.1 r.2) :=
  fill_member _ _ (fun v h => by rcases h with h | h <;> simp [h]) rows hd
    (fun r hr => by rcases hf r hr with h | h <;> simp [h])

/-- With the fix, the output domain excludes NaN only if neither the data nor the fill may hold
NaN; then no output value is NaN. So `fill_null` passes NaN on to `sum` (F21) only under a domain
that allows NaN, which `sum` rejects. -/
theorem fill_noNaN_fixed (nd nf : Bool) (h : (nd || nf) = false) (rows : List (Option F64 × F64))
    (hd : ColDom.Mem ⟨true, fun v => nd = true ∨ v ≠ nan⟩ (rows.map Prod.fst))
    (hf : ∀ r ∈ rows, nf = true ∨ r.2 ≠ nan) :
    ∀ v ∈ rows.map (fun r => fillRow r.1 r.2), v ≠ nan := by
  intro v hv
  have := fill_member_fixed nd nf rows hd hf (some v) (by simpa using hv)
  simpa [nanDom, h] using this

/-! ## Stability -/

/-- **Stability, column fill.** In a row-by-row context, the output row is a function of the input
row (`data` and `fill` are the row functions of the two child expressions), so the output is no
farther from its neighbour's than the input. -/
theorem fill_stable {R α : Type*} (data : R → Option α) (fill : R → α) (x y : List R) :
    symDist (x.map fun r => fillRow (data r) (fill r)) (y.map fun r => fillRow (data r) (fill r))
      ≤ symDist x y :=
  symDist_map_le _ x y

/-- **Stability, scalar fill.** The output is a function of each value of the data expression's
output, so it is no farther apart than the data expression's outputs, which its own stability map
bounds. -/
theorem fill_stable_scalar {α : Type*} (c : α) (dx dy : List (Option α)) :
    symDist (dx.map (fillRow · c)) (dy.map (fillRow · c)) ≤ symDist dx dy :=
  symDist_map_le _ dx dy

/-! ## F21: nulls leak through NaN -/

section Leak

variable {φ : Fmt}

/-- `clip(lo, hi)` on a float: NaN stays NaN. -/
noncomputable def clip (lo hi : ℝ) : F64 → F64
  | fin a => fin (max lo (min a hi))
  | inf false => fin hi
  | inf true => fin lo
  | nan => nan

/-- `col.fill_nan(0.0).fill_null(NaN).clip(0, 1).sum()`, the value the noise mechanism receives
(`nanToNum`: non-finite sums are rounded to a rational as `discretize_vec` does, NaN to 0). -/
noncomputable def query (φ : Fmt) (P : Plan) (xs : List (Option F64)) : ℝ :=
  nanToNum φ (reduce φ P (xs.map fun c => clip 0 1 (fillRow c nan)))

/-- A tree whose leaves all index `1.0` adds up to its number of leaves, exactly. -/
theorem eval_ones (xs : List F64) (t : STree) (h1 : ∀ i ∈ t.leaves, xs.getD i (fin 0) = fin 1)
    (hn : t.leaves.length ≤ 2 ^ φ.p) (hmax : (2 : ℝ) ^ φ.p ≤ φ.maxFinite) :
    t.eval φ xs = fin t.leaves.length := by
  induction t with
  | leaf i => simpa [STree.eval, STree.leaves] using h1 i (by simp [STree.leaves])
  | node l r ihl ihr =>
    simp only [STree.leaves, List.mem_append, List.length_append] at h1 hn ⊢
    rw [STree.eval, ihl (fun i hi => h1 i (Or.inl hi)) (by omega),
      ihr (fun i hi => h1 i (Or.inr hi)) (by omega), F64.add, F64.round]
    have hk : φ.IsRep ((l.leaves.length + r.leaves.length : ℕ) * (2 : ℝ) ^ (0 : ℤ)) :=
      Fmt.isRep_of_isRepN (Fmt.isRepN_of_le hn) (by have := φ.hp; have := φ.hemax; unfold Fmt.qmin; omega)
    simp only [zpow_zero, mul_one] at hk
    push_cast at hk ⊢
    rw [Fmt.rne_of_isRep hk, ite_eq_left]
    rw [abs_of_nonneg (by positivity)]
    calc ((l.leaves.length : ℝ) + r.leaves.length) ≤ (2 : ℝ) ^ φ.p := by exact_mod_cast hn
      _ ≤ φ.maxFinite := hmax

/-- A tree with a leaf that indexes NaN adds up to NaN. -/
theorem eval_nan (xs : List F64) (t : STree) {i : ℕ} (hi : i ∈ t.leaves)
    (h : xs.getD i (fin 0) = nan) : t.eval φ xs = nan := by
  induction t with
  | leaf j =>
    simp only [STree.leaves, List.mem_singleton] at hi
    subst hi; simpa [STree.eval] using h
  | node l r ihl ihr =>
    simp only [STree.leaves, List.mem_append] at hi
    rw [STree.eval]
    rcases hi with hi | hi
    · rw [ihl hi]; cases r.eval φ xs <;> rfl
    · rw [ihr hi]; cases l.eval φ xs <;> rfl

open Classical in
/-- Adding one row is symmetric distance 1. -/
theorem symDist_append_one {α : Type*} (x : List α) (a : α) : symDist x (x ++ [a]) = 1 := by
  unfold symDist
  rw [← Multiset.coe_add, show ((x : Multiset α) + ([a] : Multiset α)) - x = ([a] : Multiset α) from
      add_tsub_cancel_left _ _, tsub_eq_zero_of_le (Multiset.le_add_right _ _)]
  simp

/-- **F21.** `n` rows of `1.0` give `n`; with one null row added (symmetric distance 1), the null
becomes NaN, the sum NaN, and the noise mechanism receives 0. This holds for every summation
order. The sum's stability map bounds the difference by 1 (plus rounding slack), so neighbouring
datasets are distinguished: with Laplace noise of scale `b` the privacy loss is at least
`(n - 1) / b`, not the claimed `1 / b`. -/
theorem null_leak (P : Plan) (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 2 ^ φ.p)
    (hmax : (2 : ℝ) ^ φ.p ≤ φ.maxFinite) :
    let D := List.replicate n (some (fin 1))
    symDist D (D ++ [none]) = 1 ∧ query φ P D = n ∧ query φ P (D ++ [none]) = 0 := by
  intro D
  refine ⟨symDist_append_one _ _, ?_, ?_⟩
  · have hxs : D.map (fun c => clip 0 1 (fillRow c nan)) = List.replicate n (fin 1) := by
      simp [D, fillRow, clip]
    have hperm := P.perm n hn0
    unfold query reduce
    rw [hxs, ite_eq_right (by simp; omega), List.length_replicate,
      eval_ones _ _ _ (by rw [hperm.length_eq]; simpa using hn) hmax, hperm.length_eq]
    · simp [F64.nanToNum]
    · intro i hi
      have : i < n := by simpa using hperm.subset hi
      simp [List.getD_eq_getElem?_getD, this]
  · have hxs : (D ++ [none]).map (fun c => clip 0 1 (fillRow c nan)) =
        List.replicate n (fin 1) ++ [nan] := by
      simp [D, fillRow, clip]
    have hperm := P.perm (n + 1) (by omega)
    unfold query reduce
    have hi : n ∈ (P.tree (n + 1)).leaves := hperm.symm.subset (List.mem_range.mpr (by omega))
    have hget : (List.replicate n (fin 1) ++ [nan]).getD n (fin 0) = nan := by
      simp [List.getD_eq_getElem?_getD]
    rw [hxs, ite_eq_right (by simp)]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    rw [eval_nan _ _ hi hget]
    rfl

/-- The hypotheses hold for `float64`: rows of `1.0` up to `2^53`. -/
theorem null_leak_f64 (P : Plan) (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 2 ^ 53) :
    let D := List.replicate n (some (fin 1))
    symDist D (D ++ [none]) = 1 ∧ query binary64 P D = n ∧ query binary64 P (D ++ [none]) = 0 :=
  null_leak P n hn0 hn (by
    simp only [binary64, Fmt.maxFinite, Fmt.qtop]
    norm_num
    calc (9007199254740992 : ℝ) ≤ 9007199254740991 * 2 := by norm_num
      _ ≤ 9007199254740991 * 2 ^ 971 := by gcongr; exact le_self_pow₀ (by norm_num) (by norm_num))

end Leak

end OpenDP.FillNull
