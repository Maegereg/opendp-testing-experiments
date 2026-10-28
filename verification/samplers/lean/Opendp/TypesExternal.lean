-- Models of the external types used by the extracted code (Aeneas's `TypesExternal_Template.lean`,
-- filled in by hand). Trusted: listed in `verification/TRUST.md`.
module
public import Aeneas
public import Mathlib.Data.Rat.Defs
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

/-- Backtraces carry no information the samplers' outputs depend on. -/
@[rust_type "std::backtrace::Backtrace"]
def std.backtrace.Backtrace : Type := Unit

/-- A `UBig` is a natural number. -/
@[rust_type "dashu_int::ubig::UBig"]
abbrev dashu_int.ubig.UBig : Type := ℕ

/-- An `IBig` is an integer. -/
@[rust_type "dashu_int::ibig::IBig"]
abbrev dashu_int.ibig.IBig : Type := ℤ

/-- An `RBig` is a rational number (`dashu` keeps it in lowest terms, as `ℚ` does). -/
@[rust_type "dashu_ratio::rbig::RBig"]
abbrev dashu_ratio.rbig.RBig : Type := ℚ
