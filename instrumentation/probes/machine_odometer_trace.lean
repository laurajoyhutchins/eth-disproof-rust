import OAI.Algorithms.SubexponentialSAT.ExecCNFTupleOdometer

/-!
A complete step-by-step witness of the imported tuple odometer. No local
copies of source instruction tables or transition semantics. Every STEP records
its entire resulting physical machine state, so later Rust investigations can
compare or replay arbitrary prefixes without another Lean execution.

Stdout is a line protocol consumed by instrumentation/capture.py. It is not a
proof of TM2 resource bounds, nor a trace of the complete native ETH runner.
-/

namespace LeanMachineCapture
open OAI.Algorithms.SubexponentialSAT

private def bit (b : Bool) : String := if b then "1" else "0"
private def bits (xs : List Bool) : String :=
  String.ofList (xs.map fun b => if b then '1' else '0')

private def pcString {l : Nat} (pc : Option (Fin l)) : String :=
  match pc with
  | none => "-"
  | some i => toString i.val

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

private def regs {r s l : Nat} (c : BitProgram.Cfg r s l) : String :=
  String.ofList ((List.finRange r).map fun i => if c.regs i then '1' else '0')

private def stacks {r s l : Nat} (c : BitProgram.Cfg r s l) : String :=
  String.intercalate ";" ((List.finRange s).filterMap fun i =>
    let xs := c.stacks i
    if xs.isEmpty then none else some s!"{i.val}:{bits xs}")

private def machine {r s l : Nat} (stage caseName : String)
    (p : BitProgram.Program r s l) (input : List Bool) (fuel : Nat) : IO Unit := do
  IO.println s!"PROGRAM|{caseName}|{r}|{s}|{l}|{p.entry.val}|{p.inputStack.val}|{p.outputStack.val}"
  for label in List.finRange l do
    IO.println s!"CODE|{caseName}|{label.val}|{instr (p.code label)}"
  let mut c := BitProgram.initial p input
  IO.println s!"INITIAL|{caseName}|{pcString c.pc}|{regs c}|{stacks c}"
  let mut steps := 0
  for _ in [:fuel] do
    match c.pc with
    | none => break
    | some label =>
      let opcode := instr (p.code label)
      let after := BitProgram.execInstr (p.code label) c
      IO.println s!"STEP|{caseName}|{steps}|{label.val}|{opcode}|{pcString after.pc}|{regs after}|{stacks after}"
      c := after
      steps := steps + 1
  if c.pc.isSome then
    throw (IO.userError s!"{stage}/{caseName}: exceeded fuel={fuel} after {steps} instructions")
  IO.println s!"END|{caseName}|halted|{steps}|{pcString c.pc}|{regs c}|{stacks c}"

private def tupleCases : List (String × List (List Bool)) := [
  ("empty", []), ("width0", [[]]), ("one", [[false]]),
  ("two", [[false, false]]), ("split", [[false], [false]]),
  ("three", [[false, false], [false]])]

private def odometerCases : List (String × List (List Bool)) :=
  tupleCases ++ [("carry", [[true, true], [false]]), ("overflow", [[true], [true]])]

def main : IO Unit := do
  let args ← IO.getArgs
  let stage := (args[0]?).getD "all"
  let selected := (args[1]?).getD "all"
  let fuel := (((args[2]?).getD "100000").toNat?).getD 100000
  if fuel == 0 then throw (IO.userError "fuel must be positive")
  if stage != "odometer" then
    throw (IO.userError s!"unknown machine stage: {stage}")
  for (name, words) in odometerCases do
    if selected == "all" || selected == name then
      machine stage name ExecCNFTupleOdometer.program (Encoding.encodeList id words) fuel
  if selected != "all" && !(odometerCases.any fun x => x.1 == selected) then
    throw (IO.userError s!"unknown odometer case: {selected}")

end LeanMachineCapture

def main : IO Unit := LeanMachineCapture.main
