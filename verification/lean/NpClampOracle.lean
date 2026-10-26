/-
Runs the `make_np_clamp` model (`OpenDPVerification/NpClampExec.lean`) on requests, for
`verification/conformance/test_np_clamp.py`:

    lake build && lake env lean --run NpClampOracle.lean

Reads one JSON request per line and writes one JSON response per line. Floats are strings:
`"n/d"` (an exact rational), `"inf"`, `"-inf"` or `"nan"`. Requests:
* `{"op": "norm", "fmt": "f64" | "f32", "p": 1 | 2, "rows": [[x]]}`:
  `rowNorm` of each row, `{"out": [x]}`.
* `{"op": "outside", "fmt", "p", "bound": x, "origin": [x], "rows": [[x]]}`:
  `outside` of each row (the domain's norm check rejects it), `{"out": [bool]}`.
* `{"op": "clamp", "fmt", "p", "norm": x, "origin": [x], "rows": [[x]], "fuel": n}`:
  `clamp`, with the bound and origin computed from `norm` and `origin` (float64 values) as
  `make_np_clamp` does; `{"res": "ok", "bound": x, "out": [[x]]}` or `{"res": "diverge"}`.
-/
import OpenDPVerification.NpClampExec
import Lean.Data.Json

open Lean OpenDP.Float OpenDP.NpClamp OpenDP.NpClamp.Exec

def parseF (s : String) : Except String EF :=
  match s with
  | "inf" => .ok (.inf false)
  | "-inf" => .ok (.inf true)
  | "nan" => .ok .nan
  | _ =>
    match s.splitOn "/" with
    | [n, d] =>
      match n.toInt?, d.toNat? with
      | some n, some d => if d = 0 then .error s!"bad float {s}" else .ok (.fin ((n : ℚ) / d))
      | _, _ => .error s!"bad float {s}"
    | _ => .error s!"bad float {s}"

def showQ (q : ℚ) : String := s!"{q.num}/{q.den}"

def showF : EF → String
  | .fin q => showQ q
  | .inf false => "inf"
  | .inf true => "-inf"
  | .nan => "nan"

def getQ (j : Json) (k : String) : Except String ℚ := do
  match ← parseF (← j.getObjValAs? String k) with
  | .fin q => pure q
  | _ => throw s!"{k} must be finite"

def getRow (j : Json) : Except String (List EF) := do
  (← j.getArr?).toList.mapM fun v => do parseF (← v.getStr?)

def getRows (j : Json) (k : String) : Except String (List (List EF)) := do
  (← (← j.getObjVal? k).getArr?).toList.mapM getRow

def handle (j : Json) : Except String Json := do
  let φ ← match ← j.getObjValAs? String "fmt" with
    | "f64" => pure binary64
    | "f32" => pure binary32
    | f => throw s!"unknown fmt {f}"
  let ord ← match ← j.getObjValAs? Nat "p" with
    | 1 => pure Ord.l1
    | 2 => pure Ord.l2
    | p => throw s!"unknown p {p}"
  let rows ← getRows j "rows"
  match ← j.getObjValAs? String "op" with
  | "norm" =>
    pure <| Json.mkObj [("out", Json.arr (rows.map fun r =>
      Json.str (showF (rowNormQ φ numpyPlan ord r))).toArray)]
  | "outside" =>
    let bound ← getQ j "bound"
    let origin ← (← getRow (← j.getObjVal? "origin")).mapM fun
      | .fin q => pure q
      | _ => throw "origin must be finite"
    let E : ClampQ := ⟨numpyPlan, ord, bound, origin⟩
    pure <| Json.mkObj [("out", Json.arr (rows.map fun r => Json.bool (E.outside φ r)).toArray)]
  | "clamp" =>
    let norm ← getQ j "norm"
    -- `np.asarray(origin, dtype=dtype)`, then rejected unless finite
    let origin ← (← getRow (← j.getObjVal? "origin")).mapM fun
      | .fin q => match EF.round φ q with
        | .fin q => pure q
        | _ => throw "origin must be finite"
      | _ => throw "origin must be finite"
    let bound := floorFloat φ norm
    let E : ClampQ := ⟨numpyPlan, ord, bound, origin⟩
    match E.clamp φ (← j.getObjValAs? Nat "fuel") rows with
    | .ok out => pure <| Json.mkObj [("res", "ok"), ("bound", showQ bound),
        ("out", Json.arr (out.map fun r => Json.arr (r.map (Json.str ∘ showF)).toArray).toArray)]
    | .diverge => pure <| Json.mkObj [("res", "diverge")]
  | op => throw s!"unknown op {op}"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let resp := match Json.parse line >>= handle with
    | .ok r => r
    | .error e => Json.mkObj [("error", e)]
  stdout.putStrLn resp.compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
