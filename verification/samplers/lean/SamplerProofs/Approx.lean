/-
Approximate distributions: `Approx f ν ε` says that `f` returns `a` with probability at most
`ν a`, and returns at all with probability at least `1 - ε`. If `ν` is a probability distribution,
the probability that `f` returns `a` is then within `ε` of `ν a` (`Approx.close`).

The samplers are exact only up to a tiny probability of failing (a number too large for a
`usize`, which the real program cannot allocate), so their theorems are stated with `Approx`.
The rules compose: errors add up through `bindP` (`approx_bind`), and a loop whose iterations
each have error `δ` and continue with probability at most `q < 1` has error `δ / (1 - q)`
(`approx_loop`).
-/
import SamplerProofs.Tape

open Aeneas Aeneas.Std Result
open scoped ENNReal Topology

namespace OpenDP.Samplers

open Classical

/-- `f` returns `a` with probability at most `ν a`, and returns with probability at least
`1 - ε`. -/
def Approx {α : Type} (f : Prog α) (ν : α → ℝ≥0∞) (ε : ℝ≥0∞) : Prop :=
  ∃ μ, HasDist f μ ∧ (∀ a, μ a ≤ ν a) ∧ 1 ≤ (∑' a, μ a) + ε

variable {α β : Type}

theorem HasDist.eq_mass {f : Prog α} {μ : α → ℝ≥0∞} (h : HasDist f μ) (a : α) :
    μ a = mass f a :=
  (h.2 a).symm

theorem Approx.of_hasDist {f : Prog α} {μ : α → ℝ≥0∞} (h : HasDist f μ) (hμ : 1 ≤ ∑' a, μ a) :
    Approx f μ 0 :=
  ⟨μ, h, fun _ => le_rfl, by simpa using hμ⟩

theorem Approx.mono {f : Prog α} {ν ν' : α → ℝ≥0∞} {ε ε' : ℝ≥0∞} (h : Approx f ν ε)
    (hν : ∀ a, ν a ≤ ν' a) (hε : ε ≤ ε') : Approx f ν' ε' := by
  obtain ⟨μ, h1, h2, h3⟩ := h
  exact ⟨μ, h1, fun a => (h2 a).trans (hν a), h3.trans (by gcongr)⟩

theorem Approx.congr {f g : Prog α} {ν : α → ℝ≥0∞} {ε : ℝ≥0∞} (h : Approx f ν ε)
    (hfg : ∀ t, f t = g t) : Approx g ν ε := by
  have : f = g := funext hfg
  subst this
  exact h

/-- What `Approx` gives: within `ε` of a probability distribution `ν`. -/
theorem Approx.close {f : Prog α} {ν : α → ℝ≥0∞} {ε : ℝ≥0∞} (h : Approx f ν ε)
    (hν : ∑' a, ν a = 1) (a : α) : mass f a ≤ ν a ∧ ν a ≤ mass f a + ε := by
  obtain ⟨μ, h1, h2, h3⟩ := h
  rw [← h1.eq_mass]
  refine ⟨h2 a, ?_⟩
  -- `ν a + ∑_{b ≠ a} ν b = 1 ≤ μ a + ∑_{b ≠ a} μ b + ε`, and `∑_{b ≠ a} μ b ≤ ∑_{b ≠ a} ν b`.
  have hsplit : ∀ g : α → ℝ≥0∞, ∑' b, g b = g a + ∑' b, (if b = a then 0 else g b) := by
    intro g
    exact ENNReal.tsum_eq_add_tsum_ite a
  have hrest : ∑' b, (if b = a then 0 else μ b) ≤ ∑' b, (if b = a then 0 else ν b) :=
    ENNReal.tsum_le_tsum fun b => by by_cases hb : b = a <;> simp [hb, h2 b]
  have hfin : ∑' b, (if b = a then 0 else ν b) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hν, hsplit ν]
    exact le_add_self
  have := h3
  rw [hsplit μ, ← hν, hsplit ν] at this
  have : ν a + ∑' b, (if b = a then 0 else ν b) ≤
      μ a + ε + ∑' b, (if b = a then 0 else ν b) := by
    calc _ ≤ μ a + ∑' b, (if b = a then 0 else μ b) + ε := this
      _ ≤ μ a + ∑' b, (if b = a then 0 else ν b) + ε := by gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).mp this

theorem approx_pure (a : α) : Approx (fun t => ok (a, t)) (fun b => if b = a then 1 else 0) 0 :=
  Approx.of_hasDist (hasDist_pure a) (by simp)

/-- Sequencing: the errors add up. -/
theorem approx_bind {f : Prog α} {k : α → Prog β} {μ : α → ℝ≥0∞} {ν : α → β → ℝ≥0∞}
    {ε₁ ε₂ : ℝ≥0∞} (hf : Approx f μ ε₁) (hk : ∀ a, μ a ≠ 0 → Approx (k a) (ν a) ε₂)
    (hμ : ∑' a, μ a ≤ 1) :
    Approx (bindP f k) (fun b => ∑' a, μ a * ν a b) (ε₁ + ε₂) := by
  obtain ⟨μ', hμ', hle, htot⟩ := hf
  have hk' : ∀ a, ∃ ν' : β → ℝ≥0∞, μ a ≠ 0 →
      HasDist (k a) ν' ∧ (∀ b, ν' b ≤ ν a b) ∧ 1 ≤ (∑' b, ν' b) + ε₂ := by
    intro a
    by_cases h : μ a = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨ν', h1, h2, h3⟩ := hk a h
      exact ⟨ν', fun _ => ⟨h1, h2, h3⟩⟩
  choose ν' hν' using hk'
  have hpos : ∀ a, μ' a ≠ 0 → μ a ≠ 0 := fun a h h0 =>
    h (le_antisymm (h0 ▸ hle a) bot_le)
  refine ⟨fun b => ∑' a, μ' a * ν' a b,
    hasDist_bind' hμ' fun a ha => (hν' a (hpos a ha)).1, fun b => ?_, ?_⟩
  · refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases h : μ' a = 0
    · simp [h]
    · exact mul_le_mul' (hle a) ((hν' a (hpos a h)).2.1 b)
  · -- `∑_b ∑_a μ' a ν' a b = ∑_a μ' a T a`, with `1 ≤ T a + ε₂` where `μ' a ≠ 0`.
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    have hsum : ∑' a, μ' a ≤ 1 := (ENNReal.tsum_le_tsum hle).trans hμ
    have h1 : ∑' a, μ' a ≤ ∑' a, μ' a * ∑' b, ν' a b + ε₂ := by
      calc ∑' a, μ' a ≤ ∑' a, (μ' a * ∑' b, ν' a b + μ' a * ε₂) := by
            refine ENNReal.tsum_le_tsum fun a => ?_
            by_cases h : μ' a = 0
            · simp [h]
            · rw [← mul_add]
              calc μ' a = μ' a * 1 := (mul_one _).symm
                _ ≤ _ := by gcongr; exact (hν' a (hpos a h)).2.2
        _ = ∑' a, μ' a * ∑' b, ν' a b + (∑' a, μ' a) * ε₂ := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
        _ ≤ ∑' a, μ' a * ∑' b, ν' a b + ε₂ := by
            gcongr
            calc (∑' a, μ' a) * ε₂ ≤ 1 * ε₂ := by gcongr
              _ = ε₂ := one_mul _
    calc 1 ≤ ∑' a, μ' a + ε₁ := htot
      _ ≤ ∑' a, μ' a * ∑' b, ν' a b + ε₂ + ε₁ := by gcongr
      _ = _ := by ring

/-! ### Loops -/

section Loop

variable {σ S B : Type} {e : σ ≃ Tape × S}

/-- What a loop iteration's outcome contributes to the distribution of the loop's result, when
the loop, from each state `s'`, returns `b` with probability `f s' b`. -/
noncomputable def contOr (f : S → B → ℝ≥0∞) : ControlFlow S B → B → ℝ≥0∞
  | .cont s', b => f s' b
  | .done b', b => if b = b' then 1 else 0

/-- What a loop iteration's outcome contributes to the probability that the loop returns, when
it returns from each state `s'` with probability `g s'`. -/
def contTot (g : S → ℝ≥0∞) : ControlFlow S B → ℝ≥0∞
  | .cont s' => g s'
  | .done _ => 1

theorem loopCut_succ (K : S → ControlFlow S B → ℝ≥0∞) (n : ℕ) (s : S) (b : B) :
    loopCut K (n + 1) s b = ∑' c, K s c * contOr (loopCut K n) c b := by
  simp only [loopCut]
  exact tsum_congr fun c => by cases c <;> rfl

theorem tsum_contOr (f : S → B → ℝ≥0∞) (c : ControlFlow S B) :
    ∑' b, contOr f c b = contTot (fun s' => ∑' b, f s' b) c := by
  cases c with
  | cont s' => rfl
  | done b' => simp [contOr, contTot]

theorem loopCut_mono_succ (K : S → ControlFlow S B → ℝ≥0∞) :
    ∀ n s b, loopCut K n s b ≤ loopCut K (n + 1) s b
  | 0, _, _ => by simp [loopCut]
  | n + 1, s, b => by
    rw [loopCut_succ, loopCut_succ]
    refine ENNReal.tsum_le_tsum fun c => ?_
    gcongr
    cases c with
    | cont s' => exact loopCut_mono_succ K n s' b
    | done b' => exact le_rfl

/-- A sum over the outcomes of an iteration: continuing, or returning. -/
theorem tsum_controlFlow (g : ControlFlow S B → ℝ≥0∞) :
    ∑' c, g c = ∑' s', g (.cont s') + ∑' b, g (.done b) := by
  let eq : S ⊕ B ≃ ControlFlow S B :=
    { toFun := Sum.elim .cont .done
      invFun := fun c => match c with | .cont s' => .inl s' | .done b => .inr b
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun c => by cases c <;> rfl }
  rw [← eq.tsum_eq, ENNReal.summable.tsum_sum ENNReal.summable]
  rfl

/-- Truncations of a loop are below a supersolution of the loop's equation. -/
theorem loopCut_le_of_super {K K' : S → ControlFlow S B → ℝ≥0∞} {target : S → B → ℝ≥0∞}
    {I : S → Prop} (hle : ∀ s, I s → ∀ c, K s c ≤ K' s c)
    (hI : ∀ s, I s → ∀ s', K s (.cont s') ≠ 0 → I s')
    (hsup : ∀ s, I s → ∀ b, ∑' c, K' s c * contOr target c b ≤ target s b) :
    ∀ n s, I s → ∀ b, loopCut K n s b ≤ target s b := by
  intro n
  induction n with
  | zero => intro s _ b; simp [loopCut]
  | succ n ih =>
    intro s hs b
    rw [loopCut_succ]
    refine le_trans (ENNReal.tsum_le_tsum fun c => ?_) (hsup s hs b)
    by_cases hc : K s c = 0
    · simp [hc]
    · refine mul_le_mul' (hle s hs c) ?_
      cases c with
      | cont s' => exact ih s' (hI s hs s' hc) b
      | done b' => exact le_rfl

/-- The probability that a truncation returns. -/
theorem tsum_loopCut_succ (K : S → ControlFlow S B → ℝ≥0∞) (n : ℕ) (s : S) :
    ∑' b, loopCut K (n + 1) s b = ∑' c, K s c * contTot (fun s' => ∑' b, loopCut K n s' b) c := by
  simp only [loopCut_succ]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, tsum_contOr]

/-- The probability that a loop returns is the limit of that of its truncations. -/
theorem tsum_iSup_loopCut (K : S → ControlFlow S B → ℝ≥0∞) (s : S) :
    ∑' b, ⨆ n, loopCut K n s b = ⨆ n, ∑' b, loopCut K n s b := by
  have hmono : ∀ b, Monotone fun n => loopCut K n s b := fun b =>
    monotone_nat_of_le_succ fun n => loopCut_mono_succ K n s b
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone fun b _ _ h => hmono b h, ENNReal.tsum_eq_iSup_sum]
  exact iSup_comm

/-- Loops: if each iteration from a state satisfying `I` has error at most `δ`, an outcome
distribution at most `K'`, and continues with probability at most `q < 1`, and `target` is a
supersolution of the loop's equation, the loop approximates `target` within `δ / (1 - q)`. -/
theorem approx_loop {body : Body σ B} {K' : S → ControlFlow S B → ℝ≥0∞} {target : S → B → ℝ≥0∞}
    {I : S → Prop} {δ q : ℝ≥0∞}
    (hstep : ∀ s, I s → Approx (stepP e body s) (K' s) δ)
    (hI : ∀ s, I s → ∀ s', K' s (.cont s') ≠ 0 → I s')
    (hq : ∀ s, I s → ∑' s', K' s (.cont s') ≤ q) (hq1 : q < 1)
    (hsup : ∀ s, I s → ∀ b, ∑' c, K' s c * contOr target c b ≤ target s b)
    {s : S} (hs : I s) : Approx (loopP e body s) (target s) (δ * (1 - q)⁻¹) := by
  -- The distributions of the iterations.
  have hK : ∀ s, ∃ K : ControlFlow S B → ℝ≥0∞, I s →
      HasDist (stepP e body s) K ∧ (∀ c, K c ≤ K' s c) ∧ 1 ≤ (∑' c, K c) + δ := by
    intro s
    by_cases h : I s
    · obtain ⟨K, h1, h2, h3⟩ := hstep s h
      exact ⟨K, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose K hK using hK
  have hIK : ∀ s, I s → ∀ s', K s (.cont s') ≠ 0 → I s' := fun s hs s' h =>
    hI s hs s' fun h0 => h (le_antisymm (h0 ▸ (hK s hs).2.1 _) bot_le)
  have hdist := hasDist_loop_inv (fun s hs => (hK s hs).1) hIK hs
  refine ⟨_, hdist, fun b => iSup_le fun n => ?_, ?_⟩
  · -- Upper bound: every truncation is below the supersolution.
    suffices h : ∀ n s, I s → ∀ b, loopCut K n s b ≤ target s b from h n s hs b
    intro n
    induction n with
    | zero => intro s _ b; simp [loopCut]
    | succ n ih =>
      intro s hs b
      rw [loopCut_succ]
      refine le_trans (ENNReal.tsum_le_tsum fun c => ?_) (hsup s hs b)
      by_cases hc : K s c = 0
      · simp [hc]
      · refine mul_le_mul' ((hK s hs).2.1 c) ?_
        cases c with
        | cont s' => exact ih s' (hIK s hs s' hc) b
        | done b' => exact le_rfl
  · -- Lower bound: `1 ≤ T_n s + E + q^n`, where `T_n s` is the probability that the truncation
    -- returns, and `E = δ / (1 - q)`.
    set E := δ * (1 - q)⁻¹ with hE
    have hq1' : 1 - q ≠ 0 := (tsub_pos_of_lt hq1).ne'
    have hEq : q * E + δ = E := by
      have h1 : (1 - q) * E = δ := by
        rw [hE, mul_comm δ, ← mul_assoc, ENNReal.mul_inv_cancel hq1'
          (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self), one_mul]
      calc q * E + δ = q * E + (1 - q) * E := by rw [h1]
        _ = (q + (1 - q)) * E := by ring
        _ = E := by rw [add_tsub_cancel_of_le hq1.le, one_mul]
    let T : ℕ → S → ℝ≥0∞ := fun n s => ∑' b, loopCut K n s b
    have hT : ∀ n s, T (n + 1) s = ∑' c, K s c * contTot (T n) c := by
      intro n s
      simp only [T, loopCut_succ]
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left, tsum_contOr]
    have hlow : ∀ n s, I s → 1 ≤ T n s + E + q ^ n := by
      intro n
      induction n with
      | zero => intro s _; simp
      | succ n ih =>
        intro s hs
        obtain ⟨-, hle, htot⟩ := hK s hs
        have hcont : ∑' s', K s (.cont s') ≤ q :=
          (ENNReal.tsum_le_tsum fun s' => hle _).trans (hq s hs)
        -- Continuing from `s'`, the loop returns with probability `T n s'`.
        have hc : ∑' s', K s (.cont s') ≤
            ∑' s', K s (.cont s') * T n s' + q * (E + q ^ n) := by
          calc ∑' s', K s (.cont s') ≤ ∑' s', K s (.cont s') * (T n s' + (E + q ^ n)) := by
                refine ENNReal.tsum_le_tsum fun s' => ?_
                by_cases h0 : K s (.cont s') = 0
                · simp [h0]
                · calc K s (.cont s') = K s (.cont s') * 1 := (mul_one _).symm
                    _ ≤ _ := by
                        gcongr
                        rw [← add_assoc]; exact ih s' (hIK s hs s' h0)
            _ = ∑' s', K s (.cont s') * T n s' + (∑' s', K s (.cont s')) * (E + q ^ n) := by
                rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                exact tsum_congr fun s' => by ring
            _ ≤ _ := by gcongr
        rw [hT, tsum_controlFlow]
        simp only [contTot, mul_one]
        rw [tsum_controlFlow] at htot
        calc 1 ≤ ∑' s', K s (.cont s') + ∑' b, K s (.done b) + δ := htot
          _ ≤ ∑' s', K s (.cont s') * T n s' + q * (E + q ^ n) + ∑' b, K s (.done b) + δ := by
              gcongr
          _ = ∑' s', K s (.cont s') * T n s' + ∑' b, K s (.done b) + (q * E + δ) +
              q ^ (n + 1) := by ring
          _ = _ := by rw [hEq]
    -- The loop returns with probability `⨆ n, T n s`; let `n → ∞`.
    have hmono : ∀ b, Monotone fun n => loopCut K n s b := fun b =>
      monotone_nat_of_le_succ fun n => loopCut_mono_succ K n s b
    have hsupT : ∑' b, ⨆ n, loopCut K n s b = ⨆ n, T n s := by
      rw [ENNReal.tsum_eq_iSup_sum]
      simp_rw [ENNReal.finsetSum_iSup_of_monotone fun b _ _ h => hmono b h,
        T, ENNReal.tsum_eq_iSup_sum]
      exact iSup_comm
    rw [hsupT]
    have hlim : Filter.Tendsto (fun n : ℕ => (⨆ m, T m s) + E + q ^ n) Filter.atTop
        (𝓝 ((⨆ m, T m s) + E + 0)) :=
      tendsto_const_nhds.add (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1)
    rw [add_zero] at hlim
    exact ge_of_tendsto' hlim fun n =>
      (hlow n s hs).trans (by gcongr; exact le_iSup (fun m => T m s) n)

end Loop

end OpenDP.Samplers
