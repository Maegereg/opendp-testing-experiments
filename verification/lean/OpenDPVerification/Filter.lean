/-
Polars `filter`: `make_stable_filter` (`LazyFrame.filter(predicate)`,
`rust/src/transformations/make_stable_lazyframe/filter/mod.rs`) and `make_expr_filter`
(`expr.filter(by)`, `rust/src/transformations/make_stable_expr/expr_filter/mod.rs`).

The constructors build Polars plans, which Polars evaluates later. They claim:
* `make_stable_filter`: the output domain is the input's (columns unchanged), with each margin's
  invariant (public keys or lengths) dropped and its `max_length`/`max_groups` kept; the stability
  map is `d ↦ d` under the frame distance, for the symmetric, insert-delete and identifier distances.
* `make_expr_filter`, in an aggregation context: the output column's domain is the input
  expression's; each margin keeps its keys invariant (but not lengths) and `max_length`/`max_groups`;
  the stability map is `d ↦ d`.

## The model

Polars' `filter` is modelled per row (trusted, and checked by the conformance tests in
`filter/test.rs` and `expr_filter/test.rs`): the predicate is a row function with values `true`,
`false` or null, and `filter` keeps the rows whose predicate is `true`, in order (`filt`). A literal
predicate is a constant row function. In an aggregation context, `expr.filter(by)` filters each
group, and every group of the input stays in the output, empty or not.

The constructors build the predicate (and `expr`, `by`) in a row-by-row context, which the model
assumes makes them row functions. Groups (the margins' and bounds' `by`) and identifiers are row
functions too (`g`, `ident`).

## Results

* `filt_sublist`, `filt_length_le`, `filt_keys`: output rows are input rows (the column domains
  hold), groups only shrink (`max_length`), and no group appears (`max_groups`).
* `filt_symDist`, `filt_idClose`, `filt_symIdClose`: `d ↦ d` for the symmetric, insert-delete and
  identifier distances; `filt_frameClose` lifts each to the frame distance (per group, and the
  number of groups that differ). `filtMap_*`: the same for `expr.filter(by)`.
* `filt_keys_not_invariant`, `filt_lengths_not_invariant`: the invariants the constructors drop do
  not survive filtering. `make_expr_filter` keeps the keys invariant because Polars keeps empty
  groups in an aggregation (tested, not modelled).
-/
import OpenDPVerification.NpClamp

namespace OpenDP.Filter

open OpenDP.NpClamp
open scoped List

variable {R : Type*}

/-! ## Model -/

/-- Whether `filter` keeps a row whose predicate is `b` (`none` is null). -/
def keep (b : Option Bool) : Bool := b == some true

/-- `filter` with a row predicate `p`: the rows whose predicate is `true`, in order. -/
def filt (p : R → Option Bool) (xs : List R) : List R := xs.filter fun r => keep (p r)

/-- The rows of group `k` under the grouping `g`. -/
def part {K : Type*} [DecidableEq K] (g : R → K) (k : K) (xs : List R) : List R :=
  xs.filter fun r => decide (g r = k)

/-! ## The output domain -/

/-- The output is a sublist of the input: its rows are input rows, so the column domains, which
are conditions on each row, still hold. -/
theorem filt_sublist (p : R → Option Bool) (xs : List R) : filt p xs <+ xs :=
  List.filter_sublist

theorem filt_length_le (p : R → Option Bool) (xs : List R) : (filt p xs).length ≤ xs.length :=
  (filt_sublist p xs).length_le

/-- Grouping and filtering commute. -/
theorem part_filt {K : Type*} [DecidableEq K] (p : R → Option Bool) (g : R → K) (k : K)
    (xs : List R) : part g k (filt p xs) = filt p (part g k xs) := by
  unfold part filt
  rw [List.filter_filter, List.filter_filter]
  congr 1
  funext r
  exact Bool.and_comm _ _

/-- **`max_length`.** Each group of the output is no longer than the input's. -/
theorem filt_group_length_le {K : Type*} [DecidableEq K] (p : R → Option Bool) (g : R → K)
    (k : K) (xs : List R) : (part g k (filt p xs)).length ≤ (part g k xs).length := by
  rw [part_filt]; exact filt_length_le _ _

/-- **`max_groups`.** The output's group keys are among the input's. -/
theorem filt_keys {K : Type*} (p : R → Option Bool) (g : R → K) (xs : List R) :
    ∀ k ∈ (filt p xs).map g, k ∈ xs.map g := fun _ hk =>
  (((filt_sublist p xs).map g).subset hk)

/-! ## Stability -/

theorem filt_coe (p : R → Option Bool) (l : List R) :
    (filt p l : Multiset R) = Multiset.filter (fun r => keep (p r) = true) (l : Multiset R) := by
  unfold filt; rw [Multiset.filter_coe]; simp

/-- **Symmetric distance.** -/
theorem filt_symDist (p : R → Option Bool) (x y : List R) :
    symDist (filt p x) (filt p y) ≤ symDist x y := by
  classical
  unfold symDist
  rw [filt_coe, filt_coe, ← Multiset.filter_sub, ← Multiset.filter_sub]
  exact add_le_add (Multiset.card_le_card (Multiset.filter_le _ _))
    (Multiset.card_le_card (Multiset.filter_le _ _))

/-- Insert-delete closeness: `y` is reached from `x` by at most `d` insertions and deletions, that
is, they share a subsequence `z` with `|x| - |z| + |y| - |z| ≤ d`. -/
def IdClose (x y : List R) (d : ℕ) : Prop :=
  ∃ z, z <+ x ∧ z <+ y ∧ x.length + y.length ≤ d + 2 * z.length

/-- The rows `filter` drops from a sublist are no more than those it drops from the list. -/
theorem drop_le {p : R → Option Bool} {z x : List R} (h : z <+ x) :
    (z.filter fun r => !keep (p r)).length ≤ (x.filter fun r => !keep (p r)).length :=
  (h.filter _).length_le

theorem length_split (p : R → Option Bool) (x : List R) :
    x.length = (filt p x).length + (x.filter fun r => !keep (p r)).length :=
  List.length_eq_length_filter_add _

/-- **Insert-delete distance.** Filtering the shared subsequence gives one of the filtered lists:
every row dropped from it is dropped from both lists. -/
theorem filt_idClose (p : R → Option Bool) {x y : List R} {d : ℕ} (h : IdClose x y d) :
    IdClose (filt p x) (filt p y) d := by
  obtain ⟨z, hx, hy, hd⟩ := h
  refine ⟨filt p z, hx.filter _, hy.filter _, ?_⟩
  have := length_split p x; have := length_split p y; have := length_split p z
  have := drop_le (p := p) hx; have := drop_le (p := p) hy
  omega

section SymId

variable {I : Type*} [DecidableEq I]

open Classical in
/-- Identifier closeness (`SymmetricIdDistance`): the rows of each identifier in both datasets
are the same (as a multiset), and at most `d` identifiers are in only one. -/
def SymIdClose (ident : R → I) (x y : List R) (d : ℕ) : Prop :=
  (∀ i ∈ x.map ident, i ∈ y.map ident → (part ident i x : Multiset R) = part ident i y) ∧
    (((x.map ident).toFinset \ (y.map ident).toFinset).card +
      ((y.map ident).toFinset \ (x.map ident).toFinset).card) ≤ d

theorem mem_ids_iff (ident : R → I) (i : I) (x : List R) :
    i ∈ x.map ident ↔ part ident i x ≠ [] := by
  simp [part, List.filter_eq_nil_iff]

/-- Filtering rows with equal multisets gives equal multisets. -/
theorem filt_coe_eq (p : R → Option Bool) {a b : List R} (h : (a : Multiset R) = b) :
    (filt p a : Multiset R) = filt p b := by
  rw [filt_coe, filt_coe, h]

/-- An identifier in only one filtered dataset is in only one dataset. -/
theorem filt_only (ident : R → I) (p : R → Option Bool) {x y : List R}
    (hsame : ∀ i ∈ x.map ident, i ∈ y.map ident → (part ident i x : Multiset R) = part ident i y)
    {i : I} (hx : i ∈ (filt p x).map ident) (hy : i ∉ (filt p y).map ident) :
    i ∈ x.map ident ∧ i ∉ y.map ident := by
  have hx' := filt_keys p ident x i hx
  refine ⟨hx', fun hiy => hy ?_⟩
  rw [mem_ids_iff] at hx ⊢
  rw [part_filt] at hx ⊢
  intro hnil
  apply hx
  have := filt_coe_eq p (hsame i hx' hiy)
  rw [hnil] at this
  simpa using this

open Classical in
/-- **Identifier distance.** An identifier in both datasets has the same rows, so after filtering
it is in both or neither; an identifier in one filtered dataset only was in that one only. -/
theorem filt_symIdClose (ident : R → I) (p : R → Option Bool) {x y : List R} {d : ℕ}
    (h : SymIdClose ident x y d) : SymIdClose ident (filt p x) (filt p y) d := by
  obtain ⟨hsame, hd⟩ := h
  have hsame' : ∀ i, (part ident i x : Multiset R) = part ident i y →
      (part ident i (filt p x) : Multiset R) = part ident i (filt p y) := fun i h => by
    rw [part_filt, part_filt]; exact filt_coe_eq p h
  have sub (a b : List R)
      (hs : ∀ i ∈ a.map ident, i ∈ b.map ident → (part ident i a : Multiset R) = part ident i b) :
      ((filt p a).map ident).toFinset \ ((filt p b).map ident).toFinset ⊆
        (a.map ident).toFinset \ (b.map ident).toFinset := by
    intro i hi
    simp only [Finset.mem_sdiff, List.mem_toFinset] at hi ⊢
    exact filt_only ident p hs hi.1 hi.2
  have hsym : ∀ i ∈ y.map ident, i ∈ x.map ident →
      (part ident i y : Multiset R) = part ident i x := fun i hy hx => (hsame i hx hy).symm
  refine ⟨fun i hx hy => hsame' i (hsame i (filt_keys p ident x i hx) (filt_keys p ident y i hy)),
    le_trans (add_le_add (Finset.card_le_card (sub x y hsame))
      (Finset.card_le_card (sub y x hsym))) hd⟩

end SymId

/-! ## The frame distance -/

section Frame

variable {K : Type*} [DecidableEq K]

/-- Closeness under one frame-distance bound, for a grouping `g` and a closeness `Close` of the
inner metric: every group is `per`-close, and all groups but at most `num` are `0`-close
(`|s|_∞ ≤ per` and `|s|_0 ≤ num`). -/
def FrameClose (Close : List R → List R → ℕ → Prop) (g : R → K) (x y : List R)
    (num per : ℕ) : Prop :=
  (∀ k, Close (part g k x) (part g k y) per) ∧
    ∃ S : Finset K, S.card ≤ num ∧ ∀ k ∉ S, Close (part g k x) (part g k y) 0

/-- **Frame distance.** If `filter` preserves closeness for the inner metric, it preserves it for
every bound of the frame distance: each group's distance does not grow, so neither does the number
of groups that differ. -/
theorem filt_frameClose (Close : List R → List R → ℕ → Prop) (p : R → Option Bool)
    (hC : ∀ x y d, Close x y d → Close (filt p x) (filt p y) d) (g : R → K) {x y : List R}
    {num per : ℕ} (h : FrameClose Close g x y num per) :
    FrameClose Close g (filt p x) (filt p y) num per := by
  obtain ⟨hper, S, hS, hnum⟩ := h
  refine ⟨fun k => ?_, S, hS, fun k hk => ?_⟩
  · rw [part_filt, part_filt]; exact hC _ _ _ (hper k)
  · rw [part_filt, part_filt]; exact hC _ _ _ (hnum k hk)

/-- `make_stable_filter`, symmetric distance. -/
theorem filt_frame_sym (p : R → Option Bool) (g : R → K) {x y : List R} {num per : ℕ}
    (h : FrameClose (fun a b d => symDist a b ≤ d) g x y num per) :
    FrameClose (fun a b d => symDist a b ≤ d) g (filt p x) (filt p y) num per :=
  filt_frameClose _ p (fun a b d (hd : symDist a b ≤ d) => le_trans (filt_symDist p a b) hd) g h

/-- `make_stable_filter`, insert-delete distance. -/
theorem filt_frame_id (p : R → Option Bool) (g : R → K) {x y : List R} {num per : ℕ}
    (h : FrameClose IdClose g x y num per) : FrameClose IdClose g (filt p x) (filt p y) num per :=
  filt_frameClose _ p (fun _ _ _ hd => filt_idClose p hd) g h

/-- `make_stable_filter`, identifier distance. -/
theorem filt_frame_symId {I : Type*} [DecidableEq I] (ident : R → I) (p : R → Option Bool)
    (g : R → K) {x y : List R} {num per : ℕ} (h : FrameClose (SymIdClose ident) g x y num per) :
    FrameClose (SymIdClose ident) g (filt p x) (filt p y) num per :=
  filt_frameClose _ p (fun _ _ _ hd => filt_symIdClose ident p hd) g h

end Frame

/-! ## `expr.filter(by)` -/

section Expr

variable {α : Type*}

/-- `expr.filter(by)` on one group: the values of `expr` (a row function `f`) on the rows where
`by` (the row predicate `p`) is true. In an aggregation, each group is filtered on its own; by
`part_filt`, group `k` of the output is `filtMap` of group `k` of the input. -/
def filtMap (f : R → α) (p : R → Option Bool) (xs : List R) : List α := (filt p xs).map f

theorem filtMap_symDist (f : R → α) (p : R → Option Bool) (x y : List R) :
    symDist (filtMap f p x) (filtMap f p y) ≤ symDist x y :=
  le_trans (symDist_map_le f _ _) (filt_symDist p x y)

theorem idClose_map {β : Type*} (f : R → β) {x y : List R} {d : ℕ} (h : IdClose x y d) :
    IdClose (x.map f) (y.map f) d := by
  obtain ⟨z, hx, hy, hd⟩ := h
  exact ⟨z.map f, hx.map f, hy.map f, by simpa using hd⟩

theorem filtMap_idClose (f : R → α) (p : R → Option Bool) {x y : List R} {d : ℕ}
    (h : IdClose x y d) : IdClose (filtMap f p x) (filtMap f p y) d :=
  idClose_map f (filt_idClose p h)

/-- The rows of each group of the output are no more than the input's (`max_length`). -/
theorem filtMap_length_le (f : R → α) (p : R → Option Bool) (xs : List R) :
    (filtMap f p xs).length ≤ xs.length := by
  unfold filtMap; rw [List.length_map]; exact filt_length_le p xs

end Expr

/-! ## The invariants the constructors drop -/

/-- **Keys.** Two datasets with the same group keys can have different keys after `filter`, so
`make_stable_filter` drops the keys invariant. (One group `()`, with one row each; the predicate
keeps `x`'s row and drops `y`'s.) -/
theorem filt_keys_not_invariant :
    let p : Bool → Option Bool := some
    let g : Bool → Unit := fun _ => ()
    [true].map g = [false].map g ∧ (filt p [true]).map g ≠ (filt p [false]).map g := by
  simp [filt, keep]

/-- **Lengths.** Two datasets with the same group lengths can have different lengths after
`filter`, in a frame or in each group of an aggregation, so both constructors drop the lengths
invariant. -/
theorem filt_lengths_not_invariant :
    let p : Bool → Option Bool := some
    [true].length = [false].length ∧ (filt p [true]).length ≠ (filt p [false]).length := by
  simp [filt, keep]

end OpenDP.Filter
