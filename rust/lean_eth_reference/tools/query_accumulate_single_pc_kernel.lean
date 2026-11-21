import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramAccumulate

/-!
One original-source numerical accumulator instruction is checked directly by
the Lean kernel.  The input type and source callee are exactly those from the
pinned original OpenAI module.  This is a *diagnostic* on a single physical PC,
not all-site source-graph equality or a Rust-execution theorem.

The original Lean #eval observation has 309 physical labels, entry 1 and
code(1) = pop:15:0:1:2.  Unlike the previous finite-table certificates, this
proof introduces no 309-entry reified table or all-address decide.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace OAI.Algorithms.SubexponentialSAT.OriginalAccumulateSingleSite

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram

theorem original_entry_site_is_pop :
    accumulateProgram.code (1 : Fin (size accumulate + 1)) =
      Instr.pop (15 : Fin 27) (0 : Fin 8) (1 : Fin 8)
        (2 : Fin (size accumulate + 1)) := by
  rfl

end OAI.Algorithms.SubexponentialSAT.OriginalAccumulateSingleSite
