import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramAccumulate

/-!
Twelve original-source numerical accumulator instructions are checked directly by
the Lean kernel.  The input type and source callee are exactly those from the
pinned original OpenAI module.  This is a *diagnostic* across twelve selected original physical PCs,
not all-site source-graph equality or a Rust-execution theorem.

The pinned original Lean #eval observation has 309 physical labels.
Selected positions cover halt, pop, push, set, peek, branch, xor, and,
not, and goto across the full address range.  Unlike the previous finite-table certificates, this
proof introduces no 309-entry reified table or all-address decide.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace OAI.Algorithms.SubexponentialSAT.OriginalAccumulateSingleSite

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram

theorem original_pc_0_opcode :
    accumulateProgram.code (0 : Fin (size accumulate + 1)) =
      Instr.halt := by
  rfl

theorem original_pc_1_opcode :
    accumulateProgram.code (1 : Fin (size accumulate + 1)) =
      Instr.pop (15 : Fin 27) (0 : Fin 8) (1 : Fin 8) (2 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_3_opcode :
    accumulateProgram.code (3 : Fin (size accumulate + 1)) =
      Instr.push (23 : Fin 27) (0 : Fin 8) (1 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_10_opcode :
    accumulateProgram.code (10 : Fin (size accumulate + 1)) =
      Instr.set (4 : Fin 8) (false : Bool) (11 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_11_opcode :
    accumulateProgram.code (11 : Fin (size accumulate + 1)) =
      Instr.peek (18 : Fin 27) (0 : Fin 8) (1 : Fin 8) (12 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_12_opcode :
    accumulateProgram.code (12 : Fin (size accumulate + 1)) =
      Instr.branch (1 : Fin 8) (13 : Fin (size accumulate + 1)) (9 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_30_opcode :
    accumulateProgram.code (30 : Fin (size accumulate + 1)) =
      Instr.bxor (4 : Fin 8) (1 : Fin 8) (3 : Fin 8) (31 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_75_opcode :
    accumulateProgram.code (75 : Fin (size accumulate + 1)) =
      Instr.branch (4 : Fin 8) (76 : Fin (size accumulate + 1)) (287 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_103_opcode :
    accumulateProgram.code (103 : Fin (size accumulate + 1)) =
      Instr.goto (295 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_158_opcode :
    accumulateProgram.code (158 : Fin (size accumulate + 1)) =
      Instr.band (7 : Fin 8) (5 : Fin 8) (0 : Fin 8) (159 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_248_opcode :
    accumulateProgram.code (248 : Fin (size accumulate + 1)) =
      Instr.bnot (7 : Fin 8) (1 : Fin 8) (249 : Fin (size accumulate + 1)) := by
  rfl

theorem original_pc_308_opcode :
    accumulateProgram.code (308 : Fin (size accumulate + 1)) =
      Instr.goto (0 : Fin (size accumulate + 1)) := by
  rfl

end OAI.Algorithms.SubexponentialSAT.OriginalAccumulateSingleSite
