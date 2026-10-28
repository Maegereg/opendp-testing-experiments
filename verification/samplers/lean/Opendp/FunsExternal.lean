-- Models of the external functions called by the extracted code (Aeneas's
-- `FunsExternal_Template.lean`, filled in by hand). Each is the documented behavior of the Rust
-- function, panicking (`fail`) where it panics. Trusted: listed in `verification/TRUST.md`.
module
public import Aeneas
public import Opendp.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
open opendp

/-- A natural number as a `usize`, failing if it does not fit. -/
def usizeOfNat (n : ℕ) : Result Std.Usize :=
  if h : n < 2 ^ UScalarTy.Usize.numBits then ok (Usize.ofNatCore n h) else fail .integerOverflow

/-- `a.div_ceil(b)`: `⌈a / b⌉`, panicking if `b = 0`. -/
@[rust_fun "core::num::{usize}::div_ceil"]
def core.num.Usize.div_ceil (a b : Std.Usize) : Result Std.Usize :=
  if b.val = 0 then fail .divisionByZero else usizeOfNat ((a.val + b.val - 1) / b.val)

/-- `&a - b`, panicking if the difference is negative. -/
@[rust_fun
  "dashu_int::add_ops::{core::ops::arith::Sub<&'l dashu_int::ubig::UBig, dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::sub"]
def SharedLUBig.Insts.CoreOpsArithSubUBigUBig.sub (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  let a : ℕ := a; let b : ℕ := b
  if b ≤ a then ok (a - b : ℕ) else fail .panic

/-- `a.bit_len()`: the number of bits of `a` (0 for 0). -/
@[rust_fun
  "dashu_int::bits::{dashu_base::bit::BitTest<dashu_int::ubig::UBig>}::bit_len"]
def dashu_int.ubig.UBig.Insts.Dashu_baseBitBitTest.bit_len (a : dashu_int.ubig.UBig) :
    Result Std.Usize :=
  usizeOfNat (Nat.size (a : ℕ))

@[rust_fun
  "dashu_int::ubig::{core::cmp::PartialEq<dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::eq"]
def dashu_int.ubig.UBig.Insts.CoreCmpPartialEqUBig.eq (a b : dashu_int.ubig.UBig) : Result Bool :=
  ok (decide ((a : ℕ) = (b : ℕ)))

@[rust_fun
  "dashu_int::cmp::{core::cmp::PartialOrd<dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::partial_cmp"]
def dashu_int.ubig.UBig.Insts.CoreCmpPartialOrdUBig.partial_cmp (a b : dashu_int.ubig.UBig) :
    Result (Option Ordering) :=
  ok (some (compare (a : ℕ) (b : ℕ)))

/-- The value of big-endian bytes. -/
def beValue (bytes : List Std.U8) : ℕ := bytes.foldl (fun acc d => 256 * acc + d.val) 0

/-- `UBig::from_be_bytes(bytes)`. -/
@[rust_fun "dashu_int::convert::{dashu_int::ubig::UBig}::from_be_bytes"]
def dashu_int.convert.UBig.from_be_bytes (bytes : Slice Std.U8) : Result dashu_int.ubig.UBig :=
  ok (beValue bytes.val : ℕ)

/-- `&a % &b`, panicking if `b = 0`. -/
@[rust_fun
  "dashu_int::div_ops::{core::ops::arith::Rem<&'l dashu_int::ubig::UBig, &'r dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::rem"]
def SharedLUBig.Insts.CoreOpsArithRemSharedRUBigUBig.rem (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  let a : ℕ := a; let b : ℕ := b
  if b = 0 then fail .divisionByZero else ok (a % b : ℕ)

/-- `a % &b`, panicking if `b = 0`. -/
@[rust_fun
  "dashu_int::div_ops::{core::ops::arith::Rem<dashu_int::ubig::UBig, &'r dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::rem"]
def dashu_int.ubig.UBig.Insts.CoreOpsArithRemSharedRUBigUBig.rem (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  let a : ℕ := a; let b : ℕ := b
  if b = 0 then fail .divisionByZero else ok (a % b : ℕ)
