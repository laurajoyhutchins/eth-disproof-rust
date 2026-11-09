import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

/-! Execute the *actual compiled* BitProgram programs from pinned openai/math.
Each step below is BitProgram.step, never an oracle evaluator or a proof-only
statement. The terminal leaf is a checked trivial branch of the native leaf
dispatcher, NOT the general nonterminal NativeLeafProgram.command.
-/

namespace LeanPrimitiveTrace
open OAI.Algorithms.SubexponentialSAT

private def bitString (xs : List Bool) : String :=
  String.ofList (xs.map fun b => if b then '1' else '0')

private def pos (i : Fin 3) : SAT.Literal (Fin 3) := ⟨i, true⟩
private def neg (i : Fin 3) : SAT.Literal (Fin 3) := ⟨i, false⟩
private def make (clauses : List (List (SAT.Literal (Fin 3)))) : SAT.CNF (Fin 3) :=
  (clauses.map List.toFinset).toFinset

private def raw : SAT.CNF (Fin 3) :=
  make [[pos 0, neg 0], [pos 0, pos 1], [pos 0]]

private def impossible : SAT.CNF (Fin 3) :=
  make [[]]

/-- A bounded real primitive-step interpreter. Refuses unfinished computation,
rather than silently treating a capacity stop as a terminal configuration. -/
private def execute {r s l : Nat} (p : BitProgram.Program r s l)
    (start : BitProgram.Cfg r s l) (port : Fin s) (limit : Nat) :
    IO (Nat × Nat × Nat × BitProgram.Cfg r s l) := do
  let mut cfg := start
  let mut count : Nat := 0
  let mut peak : Nat := (start.stacks port).length
  let mut firstPC : Nat := p.entry.val
  while cfg.pc.isSome && count < limit do
    let some updated := BitProgram.step p cfg
      | throw (IO.userError "primitive interpreter returned none before halt")
    cfg := updated
    count := count + 1
    peak := max peak (cfg.stacks port).length
    if count == 1 then
      firstPC := (cfg.pc.map Fin.val).getD 0
  if cfg.pc.isSome then
    throw (IO.userError s!"primitive program exceeded {limit} steps")
  return (count, peak, firstPC, cfg)

private def record (name : String) (input output : List Bool)
    (steps peak firstPC : Nat) (clear : Bool) : IO Unit := do
  IO.println s!"{name}.input|{bitString input}"
  IO.println s!"{name}.output|{bitString output}"
  IO.println s!"{name}.steps|{steps}"
  IO.println s!"{name}.peak|{peak}"
  IO.println s!"{name}.pcAfter1|{firstPC}"
  IO.println s!"{name}.halted|1"
  IO.println s!"{name}.ready|{if clear then "1" else "0"}"

private def normalize (name : String) (F : SAT.CNF (Fin 3)) : IO Unit := do
  let program := SubexpNormalizationProgram.program
  let input := Encoding.encodeCNFBody F
  let start := BitProgram.initial program input
  let (steps, peak, firstPC, done) ← execute program start 13 250000
  let output := done.stacks 13
  let expected := Encoding.encodeCNFBody (SAT.normalize F)
  if output != expected then
    throw (IO.userError s!"{name}: native normalizer disagreed with SAT.normalize")
  let ready := (List.finRange 16).all fun i =>
    i == (13 : Fin 16) || done.stacks i == []
  if !ready then throw (IO.userError s!"{name}: scratch stacks not cleared")
  record name input output steps peak firstPC ready

private def terminal (name : String) (n : Nat)
    (records : List (List Bool)) (expectedCount : Nat) : IO Unit := do
  let program := SqrtLogSpace.NativeTerminal.program
  let input := Encoding.encodeList id records
  let seed := BitProgram.initial program input
  let start := { seed with «stacks» := Function.update seed.stacks
    (258 : Fin 1220) (Encoding.encodeNat n) }
  let (steps, peak, firstPC, done) ← execute program start 263 250000
  let output := done.stacks 263
  let expected := SqrtLogSpace.countWord expectedCount
  if output != expected then
    throw (IO.userError s!"{name}: native terminal count word disagreed with expected count")
  if done.stacks 258 != Encoding.encodeNat n then
    throw (IO.userError s!"{name}: ambient variable count was not retained")
  let clean := done.stacks 268 == [] && done.stacks 269 == []
  if !clean then throw (IO.userError s!"{name}: terminal scratch not cleared")
  record name input output steps peak firstPC clean

def main : IO Unit := do
  normalize "norm.empty3" (∅ : SAT.CNF (Fin 3))
  normalize "norm.false3" impossible
  normalize "norm.raw3" raw
  terminal "leaf.empty3" 3 [] 8
  terminal "leaf.false3" 3 [[false]] 0

end LeanPrimitiveTrace

def main : IO Unit := LeanPrimitiveTrace.main
