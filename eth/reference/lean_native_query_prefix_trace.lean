import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

/-!
This imports the ORIGINAL pinned OpenAI source modules. All transitions call
`BitProgram.step` on `HighQueryAdapter.prepareHighProgram`; no independent
implementation of that program is permitted in this fixture.

Pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae
Toolchain: leanprover/lean4:v4.34.1, pinned Mathlib

NOT RUN in the incomplete local Mathlib cache. The output only becomes a
cross-language oracle after genuine Lean source execution.
-/
namespace NativeQueryPrefixTrace
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

private def cases : List (String × List Bool × List Bool) := [
  ("empty", [], []),
  ("none", [false, false], []),
  ("first", [true, false, false], [true]),
  ("middle", [false, true, false], [true]),
  ("separated", [true, false, true, false], [true, false]),
  ("all", [true, true, true], [false, true, false])
]

def main : IO Unit := do
  let program := HighQueryAdapter.prepareHighProgram
  for (name, mask, high) in cases do
    let counter := Encoding.encodeList id (high.map fun b => [b])
    let stacks : Fin 896 → List Bool := fun i =>
      if i = 330 then counter
      else if i = 338 then mask
      else if i = 799 then [true]
      else if i ∈ ([702, 703, 680, 681, 682, 683, 684, 685] : List (Fin 896))
        then [false, true, false]
      else []
    let initial : BitProgram.Cfg 40 896 (StructuredCalls.size HighQueryAdapter.prepareHigh + 1) :=
      ⟨some program.entry, (fun i => decide (i = (21 : Fin 40))), stacks⟩
    let (steps, final) := run program 20000 initial
    unless final.pc.isNone do
      throw (IO.userError s!"source query-prefix program failed to halt: {name}")
    IO.println ("prepare|" ++ name ++ "|" ++ toString steps ++ "|" ++
      bits (final.stacks 330) ++ "|" ++ bits (final.stacks 338) ++ "|" ++
      bits (final.stacks 702) ++ "|" ++ bits (final.stacks 703) ++ "|" ++
      bits (final.stacks 680) ++ "|" ++ bits (final.stacks 681) ++ "|" ++
      bits (final.stacks 682) ++ "|" ++ bits (final.stacks 683) ++ "|" ++
      bits (final.stacks 684) ++ "|" ++ bits (final.stacks 685) ++ "|" ++
      bits (final.stacks 799) ++ "|" ++ bit (final.regs 21))
end NativeQueryPrefixTrace

def main : IO Unit := NativeQueryPrefixTrace.main
