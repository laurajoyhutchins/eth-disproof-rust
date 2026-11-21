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

-- Define the prepared source words once at top level. These are the exact
-- same inputs as the prior experiments, but avoid any scope ambiguity across
-- the top-level `#eval` command's elaborated do-notation.
private def sourceModulus : List Bool := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact (SubexpPreparedQuartic.canonicalModulus 2 1).bits

private def sourceCoefficient : List Bool := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact (SubexpPreparedQuartic.literalWordRun 2 1 [true]).1.val

private def sourceWidth : List Bool :=
  List.replicate (SubexpLiftRing.baseWidth 2 1) true

private def sourceCount : List Bool := [true]
private def sourceHitKey : List Bool := [true]
private def sourceMissKey : List Bool := [false]

private def sourceEntries : List (List Bool × List Bool) :=
  [(sourceHitKey, sourceCoefficient)]

private def sourceHitPresent : Bool :=
  sourceEntries.lookup sourceHitKey == some sourceCoefficient

private def sourceMissAbsent : Bool :=
  sourceEntries.lookup sourceMissKey == none

private def sourceWidthValid : Bool :=
  sourceCoefficient.length == SubexpLiftRing.baseWidth 2 1

private def runOriginalCases : IO Unit := do
  IO.println "ORIGINAL_ACCUMULATE_TRACE_V1"
  IO.println "PARAM|prime|2"
  IO.println "PARAM|exponent|1"
  IO.println s!"PARAM|width|{SubexpLiftRing.baseWidth 2 1}"
  IO.println s!"PARAM|modulus|{encodeBits sourceModulus}"
  IO.println "PARAM|entries|1"
  IO.println s!"PARAM|coefficient|{encodeBits sourceCoefficient}"
  IO.println s!"PARAM|hit_query|{encodeBits sourceHitKey}"
  IO.println s!"PARAM|miss_query|{encodeBits sourceMissKey}"
  IO.println s!"PARAM|hit_present|{sourceHitPresent}"
  IO.println s!"PARAM|miss_absent|{sourceMissAbsent}"
  IO.println s!"PARAM|width_valid|{sourceWidthValid}"
  traceCase "hit" (inputTape sourceModulus sourceWidth sourceCount
    sourceEntries sourceHitKey sourceCoefficient) 2500
  traceCase "miss" (inputTape sourceModulus sourceWidth sourceCount
    sourceEntries sourceMissKey sourceCoefficient) 2500

#eval runOriginalCases

end OriginalAccumulateHitMissTrace
