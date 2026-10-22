/-
A random tape as the state of `RandomSource`: `fill_bytes` copies the next bytes of an infinite
sequence and advances the position. A sampler's output distribution is then the push-forward of
the uniform measure on tapes (not yet defined here).
-/
import Samplers.Funs

open Aeneas Aeneas.Std Result

namespace samplers

structure Tape where
  bytes : ℕ → Std.U8
  pos : ℕ

/-- The next `n` bytes of the tape. -/
def Tape.next (t : Tape) (n : ℕ) : List Std.U8 := List.ofFn fun i : Fin n => t.bytes (t.pos + i)

/-- `fill_bytes` on a tape: never fails, fills the buffer with the next bytes. -/
def Tape.fill (t : Tape) (s : Slice Std.U8) :
    Result ((core.result.Result Unit Error) × Tape × Slice Std.U8) :=
  ok (core.result.Result.Ok (), { t with pos := t.pos + s.length },
    Slice.from (t.next s.length) (by simp [Tape.next]))

def tapeSource : RandomSource Tape := { fill_bytes := Tape.fill }

/-- The extracted `sample_standard_bernoulli` on a tape returns the low bit of the next byte and
consumes one byte. -/
theorem sample_standard_bernoulli_tape (t : Tape) :
    sample_standard_bernoulli tapeSource t =
      ok (core.result.Result.Ok (decide (t.bytes t.pos &&& 1#u8 = 1#u8)), { t with pos := t.pos + 1 }) := by
  unfold sample_standard_bernoulli
  simp [tapeSource, Tape.fill, Tape.next, lift, Array.to_slice_mut, Array.to_slice,
    core.result.Result.Insts.CoreOpsTry.branch, Array.index_usize]

end samplers
