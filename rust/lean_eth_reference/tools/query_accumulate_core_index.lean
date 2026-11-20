import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramAccumulate

/-!
Bounded executable lookup probe against the *genuine original* numerical
accumulator's compiled instruction function.

This does not use Lean.Meta, emit a graph, synthesize a substitute callee or
claim a theorem about actual Rust. A successful #eval is an original Lean
execution observation, not a kernel certificate. We intentionally query only
a few physical addresses: the full table may be enormous.
-/

namespace OriginalAccumulatorIndexedProbe

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram

private def encodeInstr {r s labels : Nat} :
    BitProgram.Instr r s labels → String
  | .halt => "halt"
  | .goto next => s!"goto:{next.val}"
  | .set dst bit next =>
      s!"set:{dst.val}:{if bit then (1 : Nat) else 0}:{next.val}"
  | .copy dst src next => s!"copy:{dst.val}:{src.val}:{next.val}"
  | .bnot dst src next => s!"not:{dst.val}:{src.val}:{next.val}"
  | .band dst a b next => s!"and:{dst.val}:{a.val}:{b.val}:{next.val}"
  | .bor dst a b next => s!"or:{dst.val}:{a.val}:{b.val}:{next.val}"
  | .bxor dst a b next => s!"xor:{dst.val}:{a.val}:{b.val}:{next.val}"
  | .branch test yes no => s!"branch:{test.val}:{yes.val}:{no.val}"
  | .push stack src next => s!"push:{stack.val}:{src.val}:{next.val}"
  | .peek stack value present next =>
      s!"peek:{stack.val}:{value.val}:{present.val}:{next.val}"
  | .pop stack value present next =>
      s!"pop:{stack.val}:{value.val}:{present.val}:{next.val}"

/-- This is the exact *original* compiled accumulator, not a replacement. -/
private abbrev sourceProgram :=
  OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.accumulateProgram

#eval do
  let p := sourceProgram
  let labels := StructuredCalls.size accumulate + 1
  IO.println s!"ORIGINAL_ACCUMULATE_LABELS={labels}"
  IO.println s!"ORIGINAL_ACCUMULATE_INPUT={p.inputStack.val}"
  IO.println s!"ORIGINAL_ACCUMULATE_OUTPUT={p.outputStack.val}"
  IO.println s!"ORIGINAL_ACCUMULATE_ENTRY={p.entry.val}"
  let exitAddress := StructuredCalls.exitAddress accumulate
  IO.println s!"ORIGINAL_ACCUMULATE_EXIT={exitAddress.val}"
  -- All labels are now observed, but only under an explicit finite bound.
  -- The subsequent independent Lean kernel certificate must still compare
  -- the observed bytes against the original source definition.
  if labels > 4096 then
    IO.println s!"ORIGINAL_ACCUMULATE_CODE_REFUSED=labels_exceed_4096"
  else
    for idx in [:labels] do
      if h : idx < labels then
        let pc : Fin labels := ⟨idx, h⟩
        IO.println s!"ORIGINAL_ACCUMULATE_CODE_AT[{idx}]={encodeInstr (p.code pc)}"
      else
        IO.println s!"ORIGINAL_ACCUMULATE_CODE_REFUSED[{idx}]=out_of_range"

end OriginalAccumulatorIndexedProbe
