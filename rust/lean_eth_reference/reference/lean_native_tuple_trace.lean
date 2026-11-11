import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer
import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleEnumeration

/-!
Source-executed traces of the *unchanged* `openai/math` finite machines,
pinned to 4eaee87548250b2682affda7d05d947c05554bae / Lean 4.34.1.

This is not a restatement or simulator of either instruction table. Every
transition calls `BitProgram.step` on a source-defined `Program`. The observer
records the physical counter word at each actual compiled callback entry.
The callback here is a two-instruction diagnostic, NOT the SAT query callback.
-/
namespace NativeTupleTrace
open OAI.Algorithms.SubexponentialSAT

private def bit (b : Bool) : String := if b then "1" else "0"
private def bits (w : List Bool) : String :=
  String.ofList (w.map fun b => if b then '1' else '0')

private def run {r s l : Nat} (p : BitProgram.Program r s l)
    (observe : Option (Fin l)) (observedPort : Fin s) :
    Nat → BitProgram.Cfg r s l → Nat × BitProgram.Cfg r s l × List (List Bool)
  | 0, c => (0, c, [])
  | fuel + 1, c =>
      match BitProgram.step p c with
      | none => (0, c, [])
      | some next =>
          let (steps, last, rest) := run p observe observedPort fuel next
          let here := if c.pc == observe then [c.stacks observedPort] else []
          (steps + 1, last, here ++ rest)

private def ports : CounterForPrograms.Ports 4 3 where
  register := Fin.castAddEmb 1
  counter := 0
  scratch := 1
  counter_ne_scratch := by decide

private def callback : StructuredCalls.Cmd 4 3 :=
  .seq (.base (.atom (.set 3 true))) (.base (.atom (.push 2 3)))

private def enumerator := ExecCNFTupleEnumeration.program ports callback

private def cases : List (String × List (List Bool)) := [
  ("empty", []),
  ("width0", [[]]),
  ("one", [[false]]),
  ("two", [[false, false]]),
  ("split", [[false], [false]]),
  ("three", [[false, false], [false]])
]

private def odometerCases : List (String × List (List Bool)) := cases ++ [
  ("carry", [[true, true], [false]]),
  ("overflow", [[true], [true]])
]

def main : IO Unit := do
  let odo := ExecCNFTupleOdometer.program
  for (name, words) in odometerCases do
    let word := Encoding.encodeList id words
    let (steps, final, _) := run odo none 0 1000 (BitProgram.initial odo word)
    unless final.pc.isNone do
      throw (IO.userError s!"source tuple odometer did not halt: {name}")
    IO.println ("odometer|" ++ name ++ "|" ++ toString steps ++ "|" ++
      bits (final.stacks 0) ++ "|" ++ bits (final.stacks 1) ++ "|" ++
      bit (final.regs 0) ++ "|" ++ bit (final.regs 1) ++ "|" ++ bit (final.regs 2))
  for (name, words) in cases do
    let word := Encoding.encodeList id words
    -- For this concrete two-instruction callback the compiled entry label is 2.
    let (steps, final, observed) := run enumerator (some 2) 0 10000
      (BitProgram.initial enumerator word)
    unless final.pc.isNone do
      throw (IO.userError s!"source tuple enumeration did not halt: {name}")
    IO.println ("enumerate|" ++ name ++ "|" ++ toString steps ++ "|" ++
      bits (final.stacks 0) ++ "|" ++ bits (final.stacks 1) ++ "|" ++
      bits (final.stacks 2) ++ "|" ++ bit (final.regs 2) ++ "|" ++
      bit (final.regs 3) ++ "|" ++ bits (Encoding.encodeList id observed))

end NativeTupleTrace

def main : IO Unit := NativeTupleTrace.main
