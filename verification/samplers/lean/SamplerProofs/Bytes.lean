/-
Byte strings and the numbers they represent: the big-endian value (`beValue`, the model of
`UBig::from_be_bytes`) is a bijection from words of length `L` to `[0, 256^L)`, so a sum over the
words of length `L` is a sum over the numbers below `256^L` (`tsum_words`).
-/
import SamplerProofs.Tape

open Aeneas Aeneas.Std
open scoped ENNReal

namespace OpenDP.Samplers

/-- Bytes are the numbers below 256. -/
def u8Equiv : Std.U8 ≃ Fin 256 where
  toFun d := ⟨d.val, by simpa using d.hBounds⟩
  invFun i := U8.ofNatCore i.val (by simp)
  left_inv d := UScalar.eq_of_val_eq (by simp [U8.ofNatCore_val_eq])
  right_inv i := Fin.ext (by simp [U8.ofNatCore_val_eq])

theorem foldl_beValue (w : List Std.U8) (acc : ℕ) :
    w.foldl (fun acc d => 256 * acc + d.val) acc = acc * 256 ^ w.length + beValue w := by
  induction w generalizing acc with
  | nil => simp [beValue]
  | cons d w ih =>
    simp only [List.foldl_cons, List.length_cons, beValue]
    rw [ih (256 * acc + d.val), ih (256 * 0 + d.val), pow_succ]
    ring

theorem beValue_cons (d : Std.U8) (w : List Std.U8) :
    beValue (d :: w) = d.val * 256 ^ w.length + beValue w := by
  have := foldl_beValue w d.val
  simpa [beValue] using this

/-- `∑_{d<k} ∑_{v<m} F (d m + v) = ∑_{x<k m} F x`. -/
theorem sum_range_mul (F : ℕ → ℝ≥0∞) (m : ℕ) :
    ∀ k, ∑ d ∈ Finset.range k, ∑ v ∈ Finset.range m, F (d * m + v) =
      ∑ x ∈ Finset.range (k * m), F x
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, sum_range_mul F m k, Nat.succ_mul, Finset.sum_range_add]

/-- Sums over the words of length `L` are sums over their values, the numbers below `256^L`. -/
theorem tsum_words (F : ℕ → ℝ≥0∞) :
    ∀ L, (∑' w : List Std.U8, if w.length = L then F (beValue w) else 0) =
      ∑ v ∈ Finset.range (256 ^ L), F v
  | 0 => by
    rw [tsum_eq_single []]
    · simp [beValue]
    · intro w hw; simp [List.length_eq_zero_iff, hw]
  | L + 1 => by
    -- Words of length `L + 1` are `d :: w` with `w` of length `L`.
    have hcons : (∑' w : List Std.U8, if w.length = L + 1 then F (beValue w) else 0) =
        ∑' p : Std.U8 × List Std.U8,
          if p.2.length = L then F (p.1.val * 256 ^ L + beValue p.2) else 0 := by
      refine tsum_eq_tsum_of_ne_zero_bij (fun p => p.1.1 :: p.1.2) ?_ ?_ ?_
      · rintro ⟨⟨d, w⟩, _⟩ ⟨⟨d', w'⟩, _⟩ e
        simp only [List.cons.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · intro w hw
        rcases w with _ | ⟨d, w⟩
        · simp at hw
        · refine ⟨⟨(d, w), ?_⟩, rfl⟩
          simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall, List.length_cons,
            add_left_inj, beValue_cons] at hw ⊢
          obtain ⟨h, hF⟩ := hw
          exact ⟨h, by rwa [h] at hF⟩
      · rintro ⟨⟨d, w⟩, _⟩
        simp only [List.length_cons, add_left_inj, beValue_cons]
        by_cases h : w.length = L <;> simp only [h, ↓reduceIte]
    rw [hcons, ENNReal.tsum_prod']
    dsimp only
    rw [tsum_congr fun d : Std.U8 => tsum_words (fun v => F (d.val * 256 ^ L + v)) L]
    rw [← u8Equiv.symm.tsum_eq, tsum_fintype]
    simp only [u8Equiv, Equiv.coe_fn_symm_mk, U8.ofNatCore_val_eq]
    rw [Fin.sum_univ_eq_sum_range (fun d => ∑ v ∈ Finset.range (256 ^ L), F (d * 256 ^ L + v)),
      sum_range_mul, pow_succ', Nat.mul_comm]

end OpenDP.Samplers
