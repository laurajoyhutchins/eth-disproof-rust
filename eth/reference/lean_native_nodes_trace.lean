import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

/-!
Direct imported-source trace for the actual QueryStreamProgram node-entry
prefix and the first source `QueryAssembler.Nodes.beginNode` command.

Pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae
Compiler: Lean 4.34.1, pinned Mathlib. NOT EXECUTED with the incomplete cache.
This is NOT a trace of the full node arithmetic, nor a callback stub.
-/
namespace NativeNodesTrace
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private def bit (b : Bool) : String := if b then "1" else "0"
private def bits (xs : List Bool) : String :=
  String.ofList (xs.map fun b => if b then '1' else '0')

private def run {r s l : Nat} (p : BitProgram.Program r s l) :
    Nat → BitProgram.Cfg r s l → Nat × BitProgram.Cfg r s l
  | 0, c => (0, c)
  | fuel + 1, c =>
    match BitProgram.step p c with
    | none => (0, c)
    | some next =>
      let (steps, final) := run p fuel next
      (steps + 1, final)

private def cases : List (String × List (List Bool)) := [
  ("empty", []),
  ("zero", [[]]),
  ("one", [[true]]),
  ("two", [[false, true], [true]]),
  ("third", [[true, false, true], [false], []]),
  ("mixed", [[false], [true, false], [false, true, true], [true]])
]

private def snapshot {l : Nat} (name : String) (entrySteps readSteps : Nat)
    (c : BitProgram.Cfg 40 896 l) : String :=
  "nodes|" ++ name ++ "|" ++ toString entrySteps ++ "|" ++ toString readSteps ++ "|" ++
    bits (c.stacks 300) ++ "|" ++ bits (c.stacks 301) ++ "|" ++
    bits (c.stacks 302) ++ "|" ++ bits (c.stacks 305) ++ "|" ++
    bits (c.stacks 307) ++ "|" ++ bits (c.stacks 78) ++ "|" ++
    bits (c.stacks 850) ++ "|" ++ bits (c.stacks 851) ++ "|" ++
    bits (c.stacks 863) ++ "|" ++ bits (c.stacks 799) ++ "|" ++
    bit (c.regs 21) ++ "|" ++ bit (c.regs 37) ++ "|" ++
    bit (c.regs 38) ++ "|" ++ bit (c.regs 39)

def main : IO Unit := do
  let cmd := StructuredCalls.Cmd.seq QueryAssembler.Nodes.initializeNodes
    QueryNodeFinish.guardCursor
  let entry := StructuredCalls.compiled cmd 300 863
  let reader := StructuredCalls.compiled QueryAssembler.Nodes.beginNode 301 78
  for (name, nodes) in cases do
    let stacks : Fin 896 → List Bool := fun i =>
      if i = 300 then Encoding.encodeList id nodes
      else if i = 301 then [true, false, true]
      else if i = 302 then [false, true]
      else if i = 305 then [true]
      else if i = 307 then [true, false]
      else if i = 78 then [false]
      else if i = 850 then [true, false]
      else if i = 851 then [false, true]
      else if i = 863 then [true]
      else if i = 799 then [true]
      else []
    let initial : BitProgram.Cfg 40 896 (StructuredCalls.size cmd + 1) :=
      ⟨some entry.entry, (fun i => decide (i = (21 : Fin 40) ∨ i = (39 : Fin 40))), stacks⟩
    let (entrySteps, arrived) := run entry 20000 initial
    unless arrived.pc.isNone do
      throw (IO.userError s!"node entry did not halt: {name}")
    if nodes.isEmpty then
      IO.println (snapshot name entrySteps 0 arrived)
    else
      let start : BitProgram.Cfg 40 896 (StructuredCalls.size QueryAssembler.Nodes.beginNode + 1) :=
        ⟨some reader.entry, arrived.regs, arrived.stacks⟩
      let (readSteps, finished) := run reader 20000 start
      unless finished.pc.isNone do
        throw (IO.userError s!"node read did not halt: {name}")
      IO.println (snapshot name entrySteps readSteps finished)
end NativeNodesTrace

def main : IO Unit := NativeNodesTrace.main
