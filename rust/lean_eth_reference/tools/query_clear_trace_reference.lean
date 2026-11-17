import Lean.Data.Json
import OAI.Algorithms.SubexponentialSAT.StackRoutines

/-!
# Independent reference steps for the original three-label clear program

Execute *BitProgram.step* from the pinned original OpenAI Lean source, not a
separately reimplemented Python or Rust transition function. Only four small
fixed inputs are enumerated here. This is finite differential evidence, not a
Lean kernel proof of all Rust programs or runtime resource bounds.
-/

open Lean
namespace OAI.Algorithms.SubexponentialSAT.PrepareClearTrace

open BitProgram StackRoutines

private def snapshot (c : Cfg 3 4 3) : Json :=
  Json.mkObj [
    ("pc", toJson (c.pc.map Fin.val)),
    ("regs", toJson (List.ofFn (fun i : Fin 3 => c.regs i))),
    ("stacks", toJson (List.ofFn (fun i : Fin 4 => c.stacks i)))
  ]

private def frames (p : Program 3 4 3) : Nat → Cfg 3 4 3 → List Json
  | 0, c => [snapshot c]
  | n + 1, c =>
    match BitProgram.step p c with
    | none => [snapshot c]
    | some next => snapshot c :: frames p n next

private def samples : List (List Bool) :=
  [[], [true], [false, true], [true, false, true]]

def runReference : IO Unit := do
  let p : Program 3 4 3 := clearProgram 1 0 1
  let mut results : List Json := []
  for word in samples do
    let c : Cfg 3 4 3 := {
      pc := some p.entry,
      regs := fun i => i.val == 2,
      «stacks» := fun i =>
        if i.val == 1 then word
        else if i.val == 3 then [false, true]
        else []
    }
    let states := frames p (2 * word.length + 3) c
    unless states.length == 2 * word.length + 4 do
      throw <| IO.userError "original Lean clearProgram trace did not halt at expected step"
    results := results ++ [Json.mkObj [
      ("word", toJson word),
      ("states", toJson states),
      ("source_steps", toJson (2 * word.length + 3))
    ]]
  let receipt := Json.mkObj [
    ("format", toJson "original-lean-clearprogram-steps-v1"),
    ("source_commit", toJson "4eaee87548250b2682affda7d05d947c05554bae"),
    ("declaration", toJson "OAI.Algorithms.SubexponentialSAT.StackRoutines.clearProgram"),
    ("r", toJson (3 : Nat)),
    ("s", toJson (4 : Nat)),
    ("labels", toJson (3 : Nat)),
    ("source_stack", toJson (1 : Nat)),
    ("value_register", toJson (0 : Nat)),
    ("present_register", toJson (1 : Nat)),
    ("cases", toJson results),
    ("independent_lean_rust_parity_proved", toJson false)
  ]
  IO.println ("ORIGINAL_LEAN_CLEAR_TRACE=" ++ receipt.compress)

end OAI.Algorithms.SubexponentialSAT.PrepareClearTrace

/-! The Lean --run entrypoint must be in the root namespace. -/
def main : IO Unit :=
  OAI.Algorithms.SubexponentialSAT.PrepareClearTrace.runReference
