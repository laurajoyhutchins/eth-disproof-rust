import NativeRust
import LCNFCapture

namespace LCNFProbe

@[noinline] def bump (x : UInt64) : UInt64 := x + 1

def select (x y : UInt64) : UInt64 :=
  let chosen := if x < y then bump x else bump y
  chosen + 5

def tailOrEmpty (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | _ :: tail => tail

end LCNFProbe

#native_rust_closure LCNFProbe.select as "select" to "artifacts/lcnf-with-pass.rs"

open Lean Elab Command

run_cmd do
  liftIO <| IO.eprintln "LCNF capture: reporting select"
  let scalar ← liftCoreM <| NativeRust.LCNFCapture.report `LCNFProbe.select
  liftIO <| IO.eprintln "LCNF capture: reporting bump"
  let helper ← liftCoreM <| NativeRust.LCNFCapture.report `LCNFProbe.bump
  -- Capture-only: no claim of supported Rust heap semantics.
  liftIO <| IO.eprintln "LCNF capture: reporting tailOrEmpty"
  let object ← liftCoreM <| NativeRust.LCNFCapture.report `LCNFProbe.tailOrEmpty
  let json := Lean.Json.mkObj [
    ("lean_version", .str "4.34.1"),
    ("declarations", .arr #[scalar, helper, object])
  ]
  liftIO <| IO.FS.writeFile "artifacts/lcnf-capture.json" json.compress
