import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramAccumulate

/-!
One independent, bounded original Lean source proof for physical labels 0..31.
The candidate 32 opcodes are copied from the original-source #eval table
artifact 14675006664 (SHA-256 0af370ad3ca3f8a5a9c0a144e8ffc82c07bc9b24acd206fa3ed863d8a58d2ea3).
This file imports no Meta exporter, has no axioms or sorry, and proves a
universally quantified equality over Fin 32 against the ORIGINAL original
compiled code function. This is not yet a whole-309-label certificate.
-/
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace OriginalAccumulatorPrefix32
open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram

private def sourcePc (i : Fin 32) : Fin 309 :=
  ⟨i.val, Nat.lt_trans i.isLt (by decide)⟩

private def observed32 (i : Fin 32) : Instr 8 27 309 :=
  (#[
    Instr.halt,
    Instr.pop (15 : Fin 27) (0 : Fin 8) (1 : Fin 8) (2 : Fin 309),
    Instr.branch (1 : Fin 8) (3 : Fin 309) (4 : Fin 309),
    Instr.push (23 : Fin 27) (0 : Fin 8) (1 : Fin 309),
    Instr.pop (23 : Fin 27) (0 : Fin 8) (1 : Fin 8) (5 : Fin 309),
    Instr.branch (1 : Fin 8) (6 : Fin 309) (8 : Fin 309),
    Instr.push (15 : Fin 27) (0 : Fin 8) (7 : Fin 309),
    Instr.push (18 : Fin 27) (0 : Fin 8) (4 : Fin 309),
    Instr.goto (10 : Fin 309),
    Instr.goto (75 : Fin 309),
    Instr.set (4 : Fin 8) false (11 : Fin 309),
    Instr.peek (18 : Fin 27) (0 : Fin 8) (1 : Fin 8) (12 : Fin 309),
    Instr.branch (1 : Fin 8) (13 : Fin 309) (9 : Fin 309),
    Instr.pop (18 : Fin 27) (0 : Fin 8) (1 : Fin 8) (14 : Fin 309),
    Instr.branch (1 : Fin 8) (15 : Fin 309) (19 : Fin 309),
    Instr.branch (0 : Fin 8) (16 : Fin 309) (19 : Fin 309),
    Instr.pop (18 : Fin 27) (0 : Fin 8) (1 : Fin 8) (17 : Fin 309),
    Instr.branch (1 : Fin 8) (18 : Fin 309) (19 : Fin 309),
    Instr.push (19 : Fin 27) (0 : Fin 8) (13 : Fin 309),
    Instr.goto (20 : Fin 309),
    Instr.pop (16 : Fin 27) (0 : Fin 8) (1 : Fin 8) (21 : Fin 309),
    Instr.branch (1 : Fin 8) (22 : Fin 309) (23 : Fin 309),
    Instr.push (21 : Fin 27) (0 : Fin 8) (20 : Fin 309),
    Instr.pop (21 : Fin 27) (0 : Fin 8) (1 : Fin 8) (24 : Fin 309),
    Instr.branch (1 : Fin 8) (25 : Fin 309) (27 : Fin 309),
    Instr.push (16 : Fin 27) (0 : Fin 8) (26 : Fin 309),
    Instr.push (20 : Fin 27) (0 : Fin 8) (23 : Fin 309),
    Instr.goto (28 : Fin 309),
    Instr.pop (19 : Fin 27) (0 : Fin 8) (1 : Fin 8) (29 : Fin 309),
    Instr.pop (20 : Fin 27) (2 : Fin 8) (3 : Fin 8) (30 : Fin 309),
    Instr.bxor (4 : Fin 8) (1 : Fin 8) (3 : Fin 8) (31 : Fin 309),
    Instr.branch (4 : Fin 8) (36 : Fin 309) (32 : Fin 309),
  ] : Array (Instr 8 27 309))[i.val]' (by simpa using i.isLt)

/-- The source program agrees with all 32 observed instruction records.
    This requires Lean kernel decidability rather than unchecked assertions. -/
theorem prefix32_all_original (i : Fin 32) :
    accumulateProgram.code (sourcePc i) = observed32 i := by
  have h : ∀ j : Fin 32, accumulateProgram.code (sourcePc j) = observed32 j := by decide
  exact h i

end OriginalAccumulatorPrefix32
