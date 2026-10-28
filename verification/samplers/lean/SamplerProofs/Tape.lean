/-
The output distributions of extracted samplers.

The extracted samplers draw their randomness from a `RandomSource`, whose state Aeneas threads
through every call. Instantiated with `tapeSource`, the state is a random tape, and a sampler is a
deterministic function `Prog α := Tape → Result (α × Tape)` of it. Its output distribution is that
of `f t` when the bytes of `t` are independent and uniform (the Proof Definition of
`RandomSource::fill_bytes`).

`HasDist f μ` says that this distribution is `μ`, a sub-probability mass function (SampCert's
`SLang`; mass missing from `μ` is the probability of diverging or failing). It is defined by
prefixes: a successful run reads finitely many bytes `w`, which occur with probability `256^-|w|`,
so `Pr[f returns a] = ∑ 256^-|w|` over the words `w` that make `f` return `a` (`Reads`). The sum
is the probability of the union of the events "the tape starts with `w`", which are disjoint
(`Reads` fixes how many bytes are read), provided every successful run is explained by such a word
(`PrefixDet`).

The rules (`hasDist_pure`, `hasDist_draw`, `hasDist_bind`, `hasDist_loop`) follow the shape of the
extracted code, so that a proof about a sampler follows its code.
-/
import Opendp
import Mathlib

open Aeneas Aeneas.Std Result
open scoped ENNReal

namespace OpenDP.Samplers

/-- A random tape: the bytes not yet read, and how many bytes have been read (from an arbitrary
origin: an integer, so that bytes can be prepended). -/
structure Tape where
  rest : ℕ → Std.U8
  count : ℤ

namespace Tape

/-- The tape after reading `n` bytes. -/
def drop (t : Tape) (n : ℕ) : Tape := ⟨fun i => t.rest (i + n), t.count + n⟩

/-- The next `n` bytes. -/
def take (t : Tape) (n : ℕ) : List Std.U8 := List.ofFn fun i : Fin n => t.rest i

/-- `t` starts with `w`. -/
def Agrees (t : Tape) (w : List Std.U8) : Prop := ∀ i (h : i < w.length), t.rest i = w[i]

/-- `w` followed by `t`. -/
def prepend (w : List Std.U8) (t : Tape) : Tape :=
  ⟨fun i => if h : i < w.length then w[i] else t.rest (i - w.length), t.count - w.length⟩

/-- A tape of zeros. -/
def zero : Tape := ⟨fun _ => 0#u8, 0⟩

@[simp] theorem count_drop (t : Tape) (n : ℕ) : (t.drop n).count = t.count + n := rfl

@[simp] theorem drop_zero (t : Tape) : t.drop 0 = t := by
  cases t; simp [drop]

theorem drop_drop (t : Tape) (m n : ℕ) : (t.drop m).drop n = t.drop (m + n) := by
  simp only [drop, Tape.mk.injEq, Nat.cast_add]
  constructor
  · funext i; congr 1; omega
  · ring

theorem drop_inj {t : Tape} {m n : ℕ} (h : t.drop m = t.drop n) : m = n := by
  have := congrArg Tape.count h
  simp at this
  exact_mod_cast this

theorem agrees_prepend (w : List Std.U8) (t : Tape) : (prepend w t).Agrees w := by
  intro i h; simp [prepend, h]

theorem drop_prepend (w : List Std.U8) (t : Tape) : (prepend w t).drop w.length = t := by
  cases t
  simp only [prepend, drop, Tape.mk.injEq]
  constructor
  · funext i; simp
  · ring

theorem agrees_append {t : Tape} {w₁ w₂ : List Std.U8} :
    t.Agrees (w₁ ++ w₂) ↔ t.Agrees w₁ ∧ (t.drop w₁.length).Agrees w₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega)
      rwa [List.getElem_append_left hi] at this
    · have := h (i + w₁.length) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [drop] using this
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hi₁ : i < w₁.length
    · rw [List.getElem_append_left hi₁]; exact h₁ i hi₁
    · rw [List.getElem_append_right (by omega)]
      have := h₂ (i - w₁.length) (by simp at hi; omega)
      simp only [drop] at this
      rwa [Nat.sub_add_cancel (by omega)] at this

theorem agrees_unique {t : Tape} {w w' : List Std.U8} (h : t.Agrees w) (h' : t.Agrees w')
    (hl : w.length = w'.length) : w = w' := by
  apply List.ext_getElem hl
  intro i hi hi'
  rw [← h i hi, ← h' i hi']

theorem agrees_take (t : Tape) (n : ℕ) : t.Agrees (t.take n) := by
  intro i h; simp [take]

end Tape

/-- The randomness source of the extracted code, reading from a tape. It never fails: the system
is assumed to have enough entropy. -/
def tapeSource : opendp.traits.samplers.RandomSource Tape where
  fill_bytes t s :=
    ok (core.result.Result.Ok (), t.drop s.length,
      Slice.from (t.take s.length) (by simp [Tape.take]))

/-- A sampler on tapes. -/
abbrev Prog (α : Type) := Tape → Result (α × Tape)

/-- `f` reads exactly `w` and returns `a`, from any tape that starts with `w`. -/
def Reads {α : Type} (f : Prog α) (w : List Std.U8) (a : α) : Prop :=
  ∀ t, t.Agrees w → f t = ok (a, t.drop w.length)

/-- Every successful run of `f` is explained by a word it reads. -/
def PrefixDet {α : Type} (f : Prog α) : Prop :=
  ∀ t a t', f t = ok (a, t') → ∃ w, t.Agrees w ∧ Reads f w a

/-- The probability of reading `w`: `256^-|w|`. -/
noncomputable def weight (w : List Std.U8) : ℝ≥0∞ := (256 : ℝ≥0∞)⁻¹ ^ w.length

open Classical in
/-- The probability that `f` returns `a`, on a uniformly random tape. -/
noncomputable def mass {α : Type} (f : Prog α) (a : α) : ℝ≥0∞ :=
  ∑' w, if Reads f w a then weight w else 0

/-- On a uniformly random tape, `f` returns `a` with probability `μ a`. -/
def HasDist {α : Type} (f : Prog α) (μ : α → ℝ≥0∞) : Prop :=
  PrefixDet f ∧ ∀ a, mass f a = μ a

/-! ### Basic facts -/

theorem weight_append (w₁ w₂ : List Std.U8) : weight (w₁ ++ w₂) = weight w₁ * weight w₂ := by
  simp [weight, pow_add]

/-- Two words that `f` reads on the same tape are equal, with equal results. -/
theorem Reads.unique {α : Type} {f : Prog α} {w w' : List Std.U8} {a a' : α} {t : Tape}
    (h : Reads f w a) (h' : Reads f w' a') (ht : t.Agrees w) (ht' : t.Agrees w') :
    w = w' ∧ a = a' := by
  have e := (h t ht).symm.trans (h' t ht')
  simp only [Result.ok.injEq, Prod.mk.injEq] at e
  exact ⟨Tape.agrees_unique ht ht' (Tape.drop_inj e.2), e.1⟩

/-- The run of `f` on a tape starting with a word it reads. -/
theorem Reads.run {α : Type} {f : Prog α} {w : List Std.U8} {a : α} {t : Tape}
    (h : Reads f w a) (ht : t.Agrees w) : f t = ok (a, t.drop w.length) := h t ht

theorem Result.cases_eq {β : Type} (m : Result β) :
    (∃ b, m = ok b) ∨ m = div ∨ ∃ e k, m = Result.vis e k := by
  cases m with
  | ret r => exact Or.inl ⟨r, rfl⟩
  | vis e k => exact Or.inr (Or.inr ⟨e, k, rfl⟩)
  | div => exact Or.inr (Or.inl rfl)

theorem bind_eq_ok {β γ : Type} {m : Result β} {k : β → Result γ} {c : γ}
    (h : Std.bind m k = ok c) : ∃ b, m = ok b ∧ k b = ok c := by
  rcases Result.cases_eq m with ⟨b, rfl⟩ | rfl | ⟨e, k', rfl⟩
  · exact ⟨b, rfl, by simpa using h⟩
  · simp at h
  · simp at h

/-! ### Rules -/

open Classical in
/-- Returning a value without reading: the point mass. -/
theorem hasDist_pure {α : Type} (a : α) :
    HasDist (fun t => ok (a, t)) (fun b => if b = a then 1 else 0) := by
  have hr : ∀ w b, Reads (fun t => ok (a, t)) w b ↔ w = [] ∧ b = a := by
    intro w b
    constructor
    · intro h
      have e := h _ (Tape.agrees_prepend w Tape.zero)
      simp only [Result.ok.injEq, Prod.mk.injEq] at e
      have hl := Tape.drop_inj ((Tape.drop_zero _).trans e.2)
      exact ⟨List.eq_nil_of_length_eq_zero hl.symm, e.1.symm⟩
    · rintro ⟨rfl, rfl⟩ t _
      simp
  refine ⟨fun t b t' h => ⟨[], fun i hi => by simp at hi, ?_⟩, fun b => ?_⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h
    exact (hr _ _).mpr ⟨rfl, h.1.symm⟩
  · simp only [mass, hr]
    by_cases hb : b = a
    · simp [hb, weight]
    · simp [hb]

/-- Draw `n` bytes. -/
def draw (n : ℕ) : Prog (List Std.U8) := fun t => ok (t.take n, t.drop n)

open Classical in
/-- Drawing `n` bytes: each word of length `n` has probability `256^-n`. -/
theorem hasDist_draw (n : ℕ) :
    HasDist (draw n) (fun w => if w.length = n then (256 : ℝ≥0∞)⁻¹ ^ n else 0) := by
  have hr : ∀ w' w, Reads (draw n) w' w ↔ w' = w ∧ w.length = n := by
    intro w' w
    constructor
    · intro h
      have ht := Tape.agrees_prepend w' Tape.zero
      have e := h _ ht
      simp only [draw, Result.ok.injEq, Prod.mk.injEq] at e
      have hl := (Tape.drop_inj e.2).symm
      have hw : w = w' := by
        rw [← e.1]
        exact Tape.agrees_unique (Tape.agrees_take _ _) ht (by simp [Tape.take, hl])
      subst hw
      exact ⟨rfl, by omega⟩
    · rintro ⟨rfl, hl⟩ t ht
      simp only [draw, Result.ok.injEq, Prod.mk.injEq, hl, and_true]
      exact Tape.agrees_unique (Tape.agrees_take _ _) ht (by simp [Tape.take, hl])
  refine ⟨fun t w t' h => ⟨w, ?_, ?_⟩, fun w => ?_⟩
  · simp only [draw, Result.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact Tape.agrees_take _ _
  · simp only [draw, Result.ok.injEq, Prod.mk.injEq] at h
    exact (hr _ _).mpr ⟨rfl, by rw [← h.1]; simp [Tape.take]⟩
  · simp only [mass, hr]
    rw [tsum_eq_single w (fun w' hw' => by simp [hw'])]
    by_cases hl : w.length = n <;> simp [hl, weight]

/-- Diverging: no mass. -/
theorem hasDist_div {α : Type} : HasDist (fun _ => (div : Result (α × Tape))) (fun _ => 0) := by
  refine ⟨fun t a t' h => by simp at h, fun a => ?_⟩
  have : ∀ w, ¬ Reads (fun _ => (div : Result (α × Tape))) w a := fun w h => by
    have := h _ (Tape.agrees_prepend w Tape.zero); simp at this
  simp [mass, this]

/-- Run `f`, then `k` on its result. -/
def bindP {α β : Type} (f : Prog α) (k : α → Prog β) : Prog β :=
  fun t => Std.bind (f t) fun p => k p.1 p.2

theorem Reads.bind {α β : Type} {f : Prog α} {k : α → Prog β} {w₁ w₂ : List Std.U8} {a : α}
    {b : β} (h₁ : Reads f w₁ a) (h₂ : Reads (k a) w₂ b) : Reads (bindP f k) (w₁ ++ w₂) b := by
  intro t ht
  rw [Tape.agrees_append] at ht
  simp only [bindP, h₁.run ht.1, bind_ok, h₂.run ht.2, Tape.drop_drop, List.length_append]

theorem PrefixDet.bind_split {α β : Type} {f : Prog α} {k : α → Prog β} (hf : PrefixDet f)
    (hk : ∀ a, PrefixDet (k a)) {t : Tape} {b : β} {t' : Tape} (h : bindP f k t = ok (b, t')) :
    ∃ a w₁ w₂, t.Agrees (w₁ ++ w₂) ∧ Reads f w₁ a ∧ Reads (k a) w₂ b ∧
      t' = t.drop (w₁ ++ w₂).length := by
  obtain ⟨⟨a, t₁⟩, h₁, h₂⟩ := bind_eq_ok h
  obtain ⟨w₁, ht₁, hr₁⟩ := hf t a t₁ h₁
  have e₁ := (hr₁.run ht₁).symm.trans h₁
  simp only [Result.ok.injEq, Prod.mk.injEq, true_and] at e₁
  subst e₁
  obtain ⟨w₂, ht₂, hr₂⟩ := hk a _ b t' h₂
  have e₂ := (hr₂.run ht₂).symm.trans h₂
  simp only [Result.ok.injEq, Prod.mk.injEq, true_and] at e₂
  refine ⟨a, w₁, w₂, Tape.agrees_append.mpr ⟨ht₁, ht₂⟩, hr₁, hr₂, ?_⟩
  rw [← e₂, Tape.drop_drop, List.length_append]

theorem PrefixDet.bind {α β : Type} {f : Prog α} {k : α → Prog β} (hf : PrefixDet f)
    (hk : ∀ a, PrefixDet (k a)) : PrefixDet (bindP f k) := by
  intro t b t' h
  obtain ⟨a, w₁, w₂, ht, hr₁, hr₂, -⟩ := hf.bind_split hk h
  exact ⟨w₁ ++ w₂, ht, hr₁.bind hr₂⟩

/-- The words read by `bindP f k` are exactly the concatenations of a word read by `f` and a
word read by its continuation. -/
theorem reads_bind_iff {α β : Type} {f : Prog α} {k : α → Prog β} (hf : PrefixDet f)
    (hk : ∀ a, PrefixDet (k a)) (w : List Std.U8) (b : β) :
    Reads (bindP f k) w b ↔ ∃ a w₁ w₂, w = w₁ ++ w₂ ∧ Reads f w₁ a ∧ Reads (k a) w₂ b := by
  constructor
  · intro h
    have ht := Tape.agrees_prepend w Tape.zero
    obtain ⟨a, w₁, w₂, ht', hr₁, hr₂, e⟩ := hf.bind_split hk (h _ ht)
    refine ⟨a, w₁, w₂, Tape.agrees_unique ht ht' (Tape.drop_inj e), hr₁, hr₂⟩
  · rintro ⟨a, w₁, w₂, rfl, hr₁, hr₂⟩
    exact hr₁.bind hr₂

open Classical in
/-- Sequencing: `Pr[bindP f k returns b] = ∑_a Pr[f returns a] Pr[k a returns b]`. -/
theorem hasDist_bind {α β : Type} {f : Prog α} {k : α → Prog β} {μ : α → ℝ≥0∞}
    {ν : α → β → ℝ≥0∞} (hf : HasDist f μ) (hk : ∀ a, HasDist (k a) (ν a)) :
    HasDist (bindP f k) (fun b => ∑' a, μ a * ν a b) := by
  refine ⟨hf.1.bind fun a => (hk a).1, fun b => ?_⟩
  -- Reindex the words read by `bindP f k` by their decompositions.
  let G : α × List Std.U8 × List Std.U8 → ℝ≥0∞ := fun p =>
    if Reads f p.2.1 p.1 ∧ Reads (k p.1) p.2.2 b then weight p.2.1 * weight p.2.2 else 0
  have hG : ∀ p : Function.support G, Reads f p.1.2.1 p.1.1 ∧ Reads (k p.1.1) p.1.2.2 b := by
    rintro ⟨p, hp⟩
    by_contra h
    exact hp (by simp [G, h])
  have hbij : mass (bindP f k) b = ∑' p, G p := by
    refine tsum_eq_tsum_of_ne_zero_bij (fun p => p.1.2.1 ++ p.1.2.2) ?_ ?_ ?_
    · rintro p q e
      obtain ⟨hp₁, hp₂⟩ := hG p
      obtain ⟨hq₁, hq₂⟩ := hG q
      have ht := Tape.agrees_prepend (p.1.2.1 ++ p.1.2.2) Tape.zero
      have htq : (Tape.prepend (p.1.2.1 ++ p.1.2.2) Tape.zero).Agrees (q.1.2.1 ++ q.1.2.2) := by
        simpa only [e] using Tape.agrees_prepend (q.1.2.1 ++ q.1.2.2) Tape.zero
      obtain ⟨e₁, ea⟩ := hp₁.unique hq₁ (Tape.agrees_append.mp ht).1 (Tape.agrees_append.mp htq).1
      have e₂ : p.1.2.2 = q.1.2.2 := by
        have := e; simp only at this; rw [e₁] at this; exact List.append_cancel_left this
      exact Subtype.ext (Prod.ext ea (Prod.ext e₁ e₂))
    · intro w hw
      have hr : Reads (bindP f k) w b := by
        by_contra h; exact hw (by simp [h])
      obtain ⟨a, w₁, w₂, rfl, hr₁, hr₂⟩ :=
        (reads_bind_iff hf.1 (fun a => (hk a).1) w b).mp hr
      refine ⟨⟨(a, w₁, w₂), ?_⟩, rfl⟩
      simp [G, hr₁, hr₂, weight]
    · rintro ⟨⟨a, w₁, w₂⟩, hp⟩
      obtain ⟨hr₁, hr₂⟩ := hG ⟨_, hp⟩
      simp [G, hr₁, hr₂, hr₁.bind hr₂, weight_append]
  rw [hbij, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [ENNReal.tsum_prod', ← (hf.2 a), ← ((hk a).2 b), mass, mass, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun w₁ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun w₂ => ?_
  by_cases h₁ : Reads f w₁ a <;> by_cases h₂ : Reads (k a) w₂ b <;> simp [G, h₁, h₂]

/-! ### Loops

Aeneas extracts a loop to `loop body x`, the least fixpoint of the unfolding equation `loop.eq_1`,
with `body x` returning `cont x'` (iterate again from `x'`) or `done y`. In the extracted samplers
the loop state starts with the tape and the result ends with it. Its distribution is the supremum
of the distributions of the loop truncated to `n` iterations (`loopCut`, SampCert's
`probWhileCut`): a successful run of the loop is a successful run of some truncation, by
fixpoint induction (`loop_ok_loopN`). -/

section Loop

open Classical WP

variable {S B : Type}

/-- A loop body, in the shape of the extracted code. -/
abbrev Body (S B : Type) := Tape × S → Result (ControlFlow (Tape × S) (B × Tape))

/-- One iteration from state `s`, as a sampler. -/
def stepP (body : Body S B) (s : S) : Prog (ControlFlow S B) := fun t =>
  Std.bind (body (t, s)) fun r => match r with
    | .cont (t', s') => ok (.cont s', t')
    | .done (b, t') => ok (.done b, t')

/-- The loop from state `s`, as a sampler. -/
def loopP (body : Body S B) (s : S) : Prog B := fun t => loop body (t, s)

/-- The loop, truncated to `n` iterations (diverging after them). -/
def loopN (body : Body S B) : ℕ → S → Prog B
  | 0, _ => fun _ => div
  | n + 1, s => bindP (stepP body s) fun c => match c with
      | .cont s' => loopN body n s'
      | .done b => fun t => ok (b, t)

/-- The distribution of a loop truncated to `n` iterations, whose iterations from state `s` have
the distribution `K s`. -/
noncomputable def loopCut (K : S → ControlFlow S B → ℝ≥0∞) : ℕ → S → B → ℝ≥0∞
  | 0, _, _ => 0
  | n + 1, s, b => ∑' c, K s c * (match c with
      | .cont s' => loopCut K n s' b
      | .done b' => if b = b' then 1 else 0)

theorem stepP_eq_ok {body : Body S B} {s : S} {t : Tape} {c : ControlFlow S B} {t₁ : Tape}
    (h : stepP body s t = ok (c, t₁)) :
    (∃ s', c = .cont s' ∧ body (t, s) = ok (.cont (t₁, s'))) ∨
      (∃ b, c = .done b ∧ body (t, s) = ok (.done (b, t₁))) := by
  obtain ⟨r, h₁, h₂⟩ := bind_eq_ok h
  rcases r with ⟨t', s'⟩ | ⟨b, t'⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    exact Or.inl ⟨s', rfl, h₁⟩
  · simp only [Result.ok.injEq, Prod.mk.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    exact Or.inr ⟨b, rfl, h₁⟩

/-- A run of a truncation that succeeds is a run of the loop. -/
theorem loopN_ok_loop {body : Body S B} :
    ∀ (n : ℕ) (s : S) (t : Tape) (r : B × Tape), loopN body n s t = ok r → loopP body s t = ok r
  | 0, s, t, r, h => by simp [loopN] at h
  | n + 1, s, t, r, h => by
    obtain ⟨⟨c, t₁⟩, h₁, h₂⟩ := bind_eq_ok h
    rw [loopP, loop.eq_1]
    rcases stepP_eq_ok h₁ with ⟨s', rfl, hb⟩ | ⟨b, rfl, hb⟩
    · rw [hb, bind_ok]
      exact loopN_ok_loop n s' t₁ r h₂
    · rw [hb, bind_ok]
      exact h₂

/-- A run of a truncation that succeeds is a run of the next truncation. -/
theorem loopN_ok_succ {body : Body S B} :
    ∀ (n : ℕ) (s : S) (t : Tape) (r : B × Tape),
      loopN body n s t = ok r → loopN body (n + 1) s t = ok r
  | 0, s, t, r, h => by simp [loopN] at h
  | n + 1, s, t, r, h => by
    obtain ⟨⟨c, t₁⟩, h₁, h₂⟩ := bind_eq_ok h
    simp only [loopN, bindP] at h ⊢
    rw [h₁, bind_ok]
    rcases c with s' | b
    · exact loopN_ok_succ n s' t₁ r h₂
    · exact h₂

/-- If the body never fails, a successful run of the loop is a successful run of a truncation
(fixpoint induction). -/
theorem loop_ok_loopN {body : Body S B} (hnf : ∀ x, dspec (body x) fun _ => True)
    {s : S} {t : Tape} {r : B × Tape} (h : loopP body s t = ok r) :
    ∃ n, loopN body n s t = ok r := by
  have key : ∀ x : Tape × S, dspec (loop body x) fun r => ∃ n, loopN body n x.2 x.1 = ok r := by
    refine loop.fixpoint_induct body (fun f => ∀ x : Tape × S,
      dspec (f x) fun r => ∃ n, loopN body n x.2 x.1 = ok r) ?_ ?_
    · exact Lean.Order.admissible_pi _ fun x => dspec_func_admissible x _
    · intro f hf x
      have hx : dspec (body x) fun r => body x = ok r := by
        have := hnf x
        rcases Result.cases_eq (body x) with ⟨b, hb⟩ | hb | ⟨e, k, hb⟩
        · rw [hb]; simp
        · rw [hb]; simp
        · rw [hb] at this; simp at this
      refine dspec_bind hx fun c hc => ?_
      rcases c with x' | ⟨b, t'⟩
      · refine dspec_mono (hf x') fun v ⟨n, hn⟩ => ⟨n + 1, ?_⟩
        simp only [loopN, bindP, stepP]
        rw [show ((x.1, x.2) : Tape × S) = x from rfl, hc, bind_ok, bind_ok]
        exact hn
      · simp only [dspec_ok]
        refine ⟨1, ?_⟩
        simp only [loopN, bindP, stepP]
        rw [show ((x.1, x.2) : Tape × S) = x from rfl, hc, bind_ok, bind_ok]
  have := key (t, s)
  rw [show loop body (t, s) = loopP body s t from rfl, h, dspec_ok] at this
  exact this

theorem hasDist_loopN {body : Body S B} {K : S → ControlFlow S B → ℝ≥0∞}
    (hK : ∀ s, HasDist (stepP body s) (K s)) :
    ∀ n s, HasDist (loopN body n s) (loopCut K n s)
  | 0, s => by
    have := @hasDist_div B
    exact ⟨this.1, fun b => (this.2 b).trans rfl⟩
  | n + 1, s => by
    have hc : ∀ c : ControlFlow S B, HasDist
        (match c with
          | .cont s' => loopN body n s'
          | .done b => fun t => ok (b, t))
        (fun b => match c with
          | .cont s' => loopCut K n s' b
          | .done b' => if b = b' then 1 else 0) := by
      intro c
      rcases c with s' | b'
      · exact hasDist_loopN hK n s'
      · exact hasDist_pure b'
    exact hasDist_bind (hK s) hc

theorem reads_loop_iff {body : Body S B} {K : S → ControlFlow S B → ℝ≥0∞}
    (hK : ∀ s, HasDist (stepP body s) (K s)) (hnf : ∀ x, dspec (body x) fun _ => True)
    (s : S) (w : List Std.U8) (b : B) :
    Reads (loopP body s) w b ↔ ∃ n, Reads (loopN body n s) w b := by
  constructor
  · intro h
    have ht := Tape.agrees_prepend w Tape.zero
    obtain ⟨n, hn⟩ := loop_ok_loopN hnf (h _ ht)
    obtain ⟨w', ht', hr⟩ := (hasDist_loopN hK n s).1 _ _ _ hn
    have e := (hr.run ht').symm.trans hn
    simp only [Result.ok.injEq, Prod.mk.injEq, true_and] at e
    exact ⟨n, (Tape.agrees_unique ht' ht (Tape.drop_inj e)) ▸ hr⟩
  · rintro ⟨n, hn⟩ t ht
    exact loopN_ok_loop n s t _ (hn t ht)

/-- Loops: if every iteration from state `s` has the distribution `K s`, and the body never
fails, the loop has the distribution `⨆ n, loopCut K n s` (SampCert's `probWhile`). -/
theorem hasDist_loop {body : Body S B} {K : S → ControlFlow S B → ℝ≥0∞}
    (hK : ∀ s, HasDist (stepP body s) (K s)) (hnf : ∀ x, dspec (body x) fun _ => True)
    (s : S) : HasDist (loopP body s) (fun b => ⨆ n, loopCut K n s b) := by
  refine ⟨fun t b t' h => ?_, fun b => ?_⟩
  · obtain ⟨n, hn⟩ := loop_ok_loopN hnf h
    obtain ⟨w, ht, hr⟩ := (hasDist_loopN hK n s).1 _ _ _ hn
    exact ⟨w, ht, (reads_loop_iff hK hnf s w b).mpr ⟨n, hr⟩⟩
  · -- The words read by the loop are the increasing union of those read by its truncations.
    let F : ℕ → List Std.U8 → ℝ≥0∞ := fun n w => if Reads (loopN body n s) w b then weight w else 0
    have hmono : ∀ w, Monotone fun n => F n w := by
      intro w
      refine monotone_nat_of_le_succ fun n => ?_
      by_cases h : Reads (loopN body n s) w b
      · have h' : Reads (loopN body (n + 1) s) w b := fun t ht => loopN_ok_succ n s t _ (h t ht)
        simp [F, h, h']
      · simp [F, h]
    have hterm : ∀ w, (if Reads (loopP body s) w b then weight w else 0) = ⨆ n, F n w := by
      intro w
      rw [reads_loop_iff hK hnf]
      by_cases h : ∃ n, Reads (loopN body n s) w b
      · obtain ⟨n, hn⟩ := h
        simp only [show ∃ n, Reads (loopN body n s) w b from ⟨n, hn⟩, ↓reduceIte]
        refine le_antisymm (le_iSup_of_le n (by simp [F, hn])) (iSup_le fun m => ?_)
        simp only [F]; split <;> simp
      · simp only [h, ↓reduceIte]
        push Not at h
        simp [F, h]
    calc mass (loopP body s) b = ∑' w, ⨆ n, F n w := tsum_congr hterm
      _ = ⨆ n, ∑' w, F n w := by
        rw [ENNReal.tsum_eq_iSup_sum]
        simp_rw [ENNReal.finsetSum_iSup_of_monotone hmono, ENNReal.tsum_eq_iSup_sum]
        exact iSup_comm
      _ = ⨆ n, loopCut K n s b := by
        congr 1; funext n; exact (hasDist_loopN hK n s).2 b

end Loop

end OpenDP.Samplers
