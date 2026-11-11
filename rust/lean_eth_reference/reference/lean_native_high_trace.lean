import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramBranches
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

/-!
Source-executed trace witness for Rust's marked-query *initializer*.
Import the UNMODIFIED openai/math sources at revision
4eaee87548250b2682affda7d05d947c05554bae with Lean 4.34.1.

This is deliberately not a local restatement of the source program. A
trace is rejected unless it comes from actual imported Lean definitions.
-/

namespace NativeHighTrace
open OAI.Algorithms.SubexponentialSAT

private def bit (b : Bool) : String := if b then "1" else "0"
private def bits (w : List Bool) : String := String.ofList (w.map fun b => if b then '1' else '0')

private def run {r s l : Nat} (p : BitProgram.Program r s l) :
    Nat → BitProgram.Cfg r s l → Nat × BitProgram.Cfg r s l
  | 0, c => (0, c)
  | fuel + 1, c =>
      match BitProgram.step p c with
      | none => (0, c)
      | some next =>
          let (steps, final) := run p fuel next
          (steps + 1, final)

private def cases : List (String × List Bool) := [
  ("empty", []),
  ("zero", [false]),
  ("one", [true]),
  ("mixed", [true, false, true]),
  ("alternate", [false, true, false, true]),
  ("all", [true, true, true, true])
]

def main : IO Unit := do
  let branch := SqrtLog.HighIncidenceProgram.Branches.program
  let init := SqrtLogSpace.HighCountSeed.initializeProgram
  for (name, mask) in cases do
    let (bsteps, b) := run branch 400 (BitProgram.initial branch mask)
    unless b.pc.isNone do
      throw (IO.userError s!"source Branches.program did not halt: {name}")
    IO.println ("branch|" ++ name ++ "|" ++ toString bsteps ++ "|" ++
      bits (b.stacks 0) ++ "|" ++ bits (b.stacks 1) ++ "|" ++
      bit (b.regs 0) ++ "|" ++ bit (b.regs 1))
    let (steps, s) := run init 1200 (BitProgram.initial init mask)
    unless s.pc.isNone do
      throw (IO.userError s!"source initializeProgram did not halt: {name}")
    IO.println ("initialize|" ++ name ++ "|" ++ toString steps ++ "|" ++
      bits (s.stacks 338) ++ "|" ++ bits (s.stacks 330) ++ "|" ++
      bits (s.stacks 789) ++ "|" ++ bit (s.regs 21))

end NativeHighTrace

def main : IO Unit := NativeHighTrace.main
