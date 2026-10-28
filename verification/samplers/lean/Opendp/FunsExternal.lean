-- Models of the external functions called by the extracted code (Aeneas's
-- `FunsExternal_Template.lean`, filled in by hand). Each is the documented behavior of the Rust
-- function, panicking (`fail`) where it panics. Trusted: listed in `verification/TRUST.md`.
module
public import Aeneas
public import Opendp.Types
public import Mathlib.Algebra.Order.Field.Rat
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

/-! ### Formatting and errors: their values do not matter to the samplers. -/

@[rust_fun "core::hint::must_use"]
def core.hint.must_use {T : Type _} (x : T) : Result T := ok x

@[rust_fun "std::backtrace::{std::backtrace::Backtrace}::capture"]
def std.backtrace.Backtrace.capture : Result std.backtrace.Backtrace := ok ()

@[rust_fun "alloc::fmt::format"]
def alloc.fmt.format (_ : core.fmt.Arguments) : Result String := ok ""

/-- `r.map(f)`. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map {T : Type _} {E : Type _} {U : Type _} {F : Type _}
    (opsfunctionFnOnceFTupleTUInst : core.ops.function.FnOnce F T U)
    (r : core.result.Result T E) (f : F) : Result (core.result.Result U E) :=
  match r with
  | .Ok t => do let u ← opsfunctionFnOnceFTupleTUInst.call_once f t; ok (.Ok u)
  | .Err e => ok (.Err e)

/-! ### `UBig` -/

@[rust_fun
  "dashu_int::add_ops::{core::ops::arith::Add<dashu_int::ubig::UBig, dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::add"]
def dashu_int.ubig.UBig.Insts.CoreOpsArithAddUBigUBig.add (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  ok (a + b : ℕ)

@[rust_fun
  "dashu_int::add_ops::{core::ops::arith::AddAssign<dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::add_assign"]
def dashu_int.ubig.UBig.Insts.CoreOpsArithAddAssignUBig.add_assign (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  ok (a + b : ℕ)

@[rust_fun
  "dashu_int::mul_ops::{core::ops::arith::Mul<dashu_int::ubig::UBig, dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::mul"]
def dashu_int.ubig.UBig.Insts.CoreOpsArithMulUBigUBig.mul (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  ok (a * b : ℕ)

/-- `a / b`, rounding down, panicking if `b = 0`. -/
@[rust_fun
  "dashu_int::div_ops::{core::ops::arith::Div<dashu_int::ubig::UBig, dashu_int::ubig::UBig, dashu_int::ubig::UBig>}::div"]
def dashu_int.ubig.UBig.Insts.CoreOpsArithDivUBigUBig.div (a b : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  let a : ℕ := a; let b : ℕ := b
  if b = 0 then fail .divisionByZero else ok (a / b : ℕ)

/-- `a % b` for a `u8` divisor, panicking if `b = 0`. -/
@[rust_fun
  "dashu_int::div_ops::{core::ops::arith::Rem<dashu_int::ubig::UBig, u8, u8>}::rem"]
def dashu_int.ubig.UBig.Insts.CoreOpsArithRemU8U8.rem (a : dashu_int.ubig.UBig) (b : Std.U8) :
    Result Std.U8 :=
  if h : b.val = 0 then fail .divisionByZero
  else ok (U8.ofNatCore ((a : ℕ) % b.val)
    (lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) b.hBounds))

@[rust_const "dashu_int::ubig::{dashu_int::ubig::UBig}::ZERO"]
def dashu_int.ubig.UBig.ZERO : Result dashu_int.ubig.UBig := ok (0 : ℕ)

@[rust_const "dashu_int::ubig::{dashu_int::ubig::UBig}::ONE"]
def dashu_int.ubig.UBig.ONE : Result dashu_int.ubig.UBig := ok (1 : ℕ)

@[rust_fun
  "dashu_int::ubig::{core::clone::Clone<dashu_int::ubig::UBig>}::clone"]
def dashu_int.ubig.UBig.Insts.CoreCloneClone.clone (a : dashu_int.ubig.UBig) :
    Result dashu_int.ubig.UBig :=
  ok a

/-- `u.as_ibig()`: the same number, as an integer. -/
@[rust_fun "dashu_int::convert::{dashu_int::ubig::UBig}::as_ibig"]
def dashu_int.convert.UBig.as_ibig (a : dashu_int.ubig.UBig) : Result dashu_int.ibig.IBig :=
  ok ((a : ℕ) : ℤ)

/-! ### `IBig` -/

@[rust_fun
  "dashu_int::convert::{core::convert::From<dashu_int::ibig::IBig, i32>}::from"]
def dashu_int.ibig.IBig.Insts.CoreConvertFromI32.from (x : Std.I32) : Result dashu_int.ibig.IBig :=
  ok x.val

/-- `z.into_parts()`: the sign (`Positive` for zero) and the magnitude. -/
@[rust_fun "dashu_int::ibig::{dashu_int::ibig::IBig}::into_parts"]
def dashu_int.ibig.IBig.into_parts (z : dashu_int.ibig.IBig) :
    Result (dashu_base.sign.Sign × dashu_int.ubig.UBig) :=
  let z : ℤ := z
  ok (if z < 0 then .Negative else .Positive, z.natAbs)

@[rust_fun "dashu_int::ibig::{dashu_int::ibig::IBig}::is_zero"]
def dashu_int.ibig.IBig.is_zero (z : dashu_int.ibig.IBig) : Result Bool := ok (decide ((z : ℤ) = 0))

@[rust_fun
  "dashu_int::ibig::{core::clone::Clone<dashu_int::ibig::IBig>}::clone"]
def dashu_int.ibig.IBig.Insts.CoreCloneClone.clone (z : dashu_int.ibig.IBig) :
    Result dashu_int.ibig.IBig :=
  ok z

@[rust_fun
  "dashu_int::sign::{core::ops::arith::Neg<dashu_int::ibig::IBig, dashu_int::ibig::IBig>}::neg"]
def dashu_int.ibig.IBig.Insts.CoreOpsArithNegIBig.neg (z : dashu_int.ibig.IBig) :
    Result dashu_int.ibig.IBig :=
  ok (-(z : ℤ))

/-! ### `RBig` -/

@[rust_fun
  "dashu_ratio::add::{core::ops::arith::SubAssign<dashu_ratio::rbig::RBig, dashu_ratio::rbig::RBig>}::sub_assign"]
def dashu_ratio.rbig.RBig.Insts.CoreOpsArithSubAssignRBig.sub_assign (a b : dashu_ratio.rbig.RBig) :
    Result dashu_ratio.rbig.RBig :=
  ok ((a : ℚ) - b)

@[rust_fun
  "dashu_ratio::cmp::{core::cmp::PartialEq<dashu_ratio::rbig::RBig, dashu_ratio::rbig::RBig>}::eq"]
def dashu_ratio.rbig.RBig.Insts.CoreCmpPartialEqRBig.eq (a b : dashu_ratio.rbig.RBig) :
    Result Bool :=
  ok (decide ((a : ℚ) = b))

@[rust_fun
  "dashu_ratio::convert::{core::convert::From<dashu_ratio::rbig::RBig, i32>}::from"]
def dashu_ratio.rbig.RBig.Insts.CoreConvertFromI32.from (x : Std.I32) :
    Result dashu_ratio.rbig.RBig :=
  ok ((x.val : ℤ) : ℚ)

/-- `x / &u`, panicking if `u = 0`. -/
@[rust_fun
  "dashu_ratio::div::{core::ops::arith::Div<dashu_ratio::rbig::RBig, &'r dashu_int::ubig::UBig, dashu_ratio::rbig::RBig>}::div"]
def dashu_ratio.rbig.RBig.Insts.CoreOpsArithDivSharedRUBigRBig.div (a : dashu_ratio.rbig.RBig)
    (b : dashu_int.ubig.UBig) : Result dashu_ratio.rbig.RBig :=
  if (b : ℕ) = 0 then fail .divisionByZero else ok ((a : ℚ) / ((b : ℕ) : ℚ))

@[rust_fun
  "dashu_ratio::rbig::{core::cmp::PartialOrd<dashu_ratio::rbig::RBig, dashu_ratio::rbig::RBig>}::partial_cmp"]
def dashu_ratio.rbig.RBig.Insts.CoreCmpPartialOrdRBig.partial_cmp (a b : dashu_ratio.rbig.RBig) :
    Result (Option Ordering) :=
  ok (some (compare (a : ℚ) b))

@[rust_const "dashu_ratio::rbig::{dashu_ratio::rbig::RBig}::ONE"]
def dashu_ratio.rbig.RBig.ONE : Result dashu_ratio.rbig.RBig := ok (1 : ℚ)

/-- `RBig::from_parts(n, d)`: `n / d`, panicking if `d = 0`. -/
@[rust_fun "dashu_ratio::rbig::{dashu_ratio::rbig::RBig}::from_parts"]
def dashu_ratio.rbig.RBig.from_parts (n : dashu_int.ibig.IBig) (d : dashu_int.ubig.UBig) :
    Result dashu_ratio.rbig.RBig :=
  if (d : ℕ) = 0 then fail .panic else ok ((n : ℤ) / ((d : ℕ) : ℚ))

/-- `x.into_parts()`: numerator and denominator in lowest terms. -/
@[rust_fun "dashu_ratio::rbig::{dashu_ratio::rbig::RBig}::into_parts"]
def dashu_ratio.rbig.RBig.into_parts (x : dashu_ratio.rbig.RBig) :
    Result (dashu_int.ibig.IBig × dashu_int.ubig.UBig) :=
  ok ((x : ℚ).num, (x : ℚ).den)

@[rust_fun "dashu_ratio::rbig::{dashu_ratio::rbig::RBig}::is_zero"]
def dashu_ratio.rbig.RBig.is_zero (x : dashu_ratio.rbig.RBig) : Result Bool :=
  ok (decide ((x : ℚ) = 0))

@[rust_fun
  "dashu_ratio::rbig::{core::clone::Clone<dashu_ratio::rbig::RBig>}::clone"]
def dashu_ratio.rbig.RBig.Insts.CoreCloneClone.clone (x : dashu_ratio.rbig.RBig) :
    Result dashu_ratio.rbig.RBig :=
  ok x
