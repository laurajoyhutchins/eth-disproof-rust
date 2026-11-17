import Lean.Data.Json
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCountPrepare

/-!
Evaluate only the original pinned Count.Prepare.ports definition as a finite
List (Fin 768). This is an independent runtime observation from the compiled
original Lean source, not a kernel certificate or executable Rust lowering.
-/
def main : IO Unit := do
  let sourcePorts : List (Fin 768) :=
    OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.Prepare.ports
  let values : List Nat := sourcePorts.map (fun i => i.val)
  IO.println ("ORIGINAL_PREPARE_PORTS_JSON=" ++ (Lean.Json.compress (Lean.toJson values)))
