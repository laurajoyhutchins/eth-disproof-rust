import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

/-!
Exports the EXACT pinned QueryStreamProgram.program finite source table.
Run from the pinned upstream Lean checkout after a successful import Mathlib.
This is not a Rust substitute or an unverified hand-written table.
Output is streamed to stdout, line by line, for the strict Rust importer.
The input must be clean at openai/math@4eaee87548250b2682affda7d05d947c05554bae.
-/

namespace NativeQueryTableExport
open OAI.Algorithms.SubexponentialSAT

private def bit (b : Bool) : String := if b then "1" else "0"

private def instr {r s l : Nat} : BitProgram.Instr r s l → String
  | .halt => "halt"
  | .goto n => s!"goto:{n.val}"
  | .set d v n => s!"set:{d.val}:{bit v}:{n.val}"
  | .copy d a n => s!"copy:{d.val}:{a.val}:{n.val}"
  | .bnot d a n => s!"not:{d.val}:{a.val}:{n.val}"
  | .band d a b n => s!"and:{d.val}:{a.val}:{b.val}:{n.val}"
  | .bor d a b n => s!"or:{d.val}:{a.val}:{b.val}:{n.val}"
  | .bxor d a b n => s!"xor:{d.val}:{a.val}:{b.val}:{n.val}"
  | .branch t y n => s!"branch:{t.val}:{y.val}:{n.val}"
  | .push s a n => s!"push:{s.val}:{a.val}:{n.val}"
  | .peek s v p n => s!"peek:{s.val}:{v.val}:{p.val}:{n.val}"
  | .pop s v p n => s!"pop:{s.val}:{v.val}:{p.val}:{n.val}"

def main : IO Unit := do
  let args ← IO.getArgs
  let cap := (((args[0]?).getD "2000000").toNat?).getD 0
  if cap == 0 then throw (IO.userError "positive maximum label count required")
  let labelCount := StructuredCalls.size SqrtLogSpace.QueryStreamProgram.command + 1
  if labelCount > cap then
    throw (IO.userError s!"source-defined query table has {labelCount} labels, above cap {cap}")
  let p := SqrtLogSpace.QueryStreamProgram.program
  IO.println "PIN|query|4eaee87548250b2682affda7d05d947c05554bae|c2fb29983bb33229d5cf60729cd3d1e37b9b00ca"
  IO.println s!"PROGRAM|query|40|896|{labelCount}|{p.entry.val}|{p.inputStack.val}|{p.outputStack.val}"
  for label in List.finRange labelCount do
    IO.println s!"CODE|query|{label.val}|{instr (p.code label)}"
  IO.println s!"END|query|{labelCount}"

end NativeQueryTableExport

def main : IO Unit := NativeQueryTableExport.main
