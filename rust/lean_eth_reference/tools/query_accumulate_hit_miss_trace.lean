import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramAccumulate

/-!
Source-native, bounded trace experiment on the **original OpenAI** numerical
accumulator. Uses the genuine Dictionary.inputTape, a canonical p=2, mu=1
modulus, one fixed-width coefficient and the original Program.code at every
step. No Meta exporter, no handwritten tape encoding or replacement algorithm.

This is executable original-Lean evidence, NOT a kernel certificate of the
separate 309-row JSON observation and not a Lean-to-Rust refinement theorem.
A step limit yields an explicit CAPPED refusal, never a fabricated termination.
-/

namespace OriginalAccumulateHitMissTrace

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

private def encodeBits (xs : List Bool) : String :=
  String.ofList (xs.map fun x => if x then '1' else '0')

private def frame {l : Nat} (c : BitProgram.Cfg 8 27 l) : String :=
  let pc := match c.pc with
    | none => "X"
    | some j => toString j.val
  let regs := encodeBits (List.ofFn fun j : Fin 8 => c.regs j)
  let stackText := String.intercalate "," ((List.ofFn fun j : Fin 27 =>
    encodeBits (c.stacks j)) : List String)
  s!"{pc}|{regs}|{stackText}"

private def traceCase (label : String) (tape : Tape)
    (maxSteps : Nat) : IO Unit := do
  let source := accumulateProgram
  let mut c : BitProgram.Cfg 8 27 (StructuredCalls.size accumulate + 1) :=
    (machine (fun _ => false) tape).withPC (some source.entry)
  let mut steps := 0
  IO.println s!"TRACE|{label}|0|{frame c}"
  for _ in [:maxSteps] do
    if c.pc.isNone then
      break
    match BitProgram.step source c with
    | none => throw (IO.userError "unexpected original step None before halt")
    | some next =>
      c := next
      steps := steps + 1
      IO.println s!"TRACE|{label}|{steps}|{frame c}"
  let status := if c.pc.isNone then "HALTED" else "CAPPED"
  IO.println s!"END|{label}|{steps}|{status}"

private def runOriginalCases : IO Unit := do
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let modulus := (SubexpPreparedQuartic.canonicalModulus 2 1).bits
  let width := List.replicate (SubexpLiftRing.baseWidth 2 1) true
  let count := [true]
  let one := (SubexpPreparedQuartic.literalWordRun 2 1 [true]).1.val
  let entries : List (List Bool × List Bool) := [([true], one)]
  let hitQuery := [true]
  let missQuery := [false]
  let validInputs : Bool :=
    (entries.lookup hitQuery == some one) &&
    (entries.lookup missQuery == none) &&
    (one.length == SubexpLiftRing.baseWidth 2 1)
  if validInputs then
    pure ()
  else
    throw (IO.userError "original dictionary hit/miss or coefficient width refused")
  IO.println "ORIGINAL_ACCUMULATE_TRACE_V1"
  IO.println s!"PARAM|prime|2"
  IO.println s!"PARAM|exponent|1"
  IO.println s!"PARAM|width|{SubexpLiftRing.baseWidth 2 1}"
  IO.println s!"PARAM|modulus|{encodeBits modulus}"
  IO.println s!"PARAM|entries|1"
  IO.println s!"PARAM|coefficient|{encodeBits one}"
  IO.println s!"PARAM|hit_query|{encodeBits hitQuery}"
  IO.println s!"PARAM|miss_query|{encodeBits missQuery}"
  traceCase "hit" (inputTape modulus width count entries hitQuery one) 2500
  traceCase "miss" (inputTape modulus width count entries missQuery one) 2500

#eval runOriginalCases

end OriginalAccumulateHitMissTrace
