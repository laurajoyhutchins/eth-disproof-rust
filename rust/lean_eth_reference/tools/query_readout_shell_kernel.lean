import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgramNative

/-!
# Source-indexed readout shell, without the Meta exporter

This imports the *pinned original* OpenAI readout module, but no Lean.Meta
traversal or second importer. The numerical row remains opaque.

Each theorem refers to the genuine original source declarations.
It proves a boundary in Lean: source constructor identity, static site
accounting, exact source-level Eval composition, and instruction lookup at
all source sites plus the final halt. No theorem claims that Rust has
implemented the numerical program or that the original import is cheap.
-/

namespace OAI.Algorithms.SubexponentialSAT.ReadoutShell

open OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram

/-- The actual source preparation, with its ordered mask/copy operations. -/
theorem prepare_source :
    prepare = .seq makeMask (wcopy 29 33 23) := rfl

/-- The actual source finishing command, with its ordered transfer/clears. -/
theorem finish_source :
    finish = .seq (wtransfer 35 0) (.seq (wclear 31) (wclear 34)) := rfl

/-- Runtime iteration is a while loop, not static unrolling of the J counter.
    The source uses `forCmd`, which initially pops once, then repeats a row
    and one further pop while the flag remains true. -/
theorem outer_source :
    outer =
      .seq (UnaryForPrograms.popCmd outerPorts)
        (.while outerPorts.flag
          (.seq row (UnaryForPrograms.popCmd outerPorts))) := rfl

/-- The complete original readout retains exactly this nested source tree. -/
theorem command_source :
    command = .seq prepare (.seq outer finish) := rfl

/-- Source compilation, including the original local input 15 and output 0.
    This equality does not reconstruct a flattened physical instruction table. -/
theorem program_source :
    program = StructuredCalls.compiled command (15 : Fin 40) (0 : Fin 40) := rfl

/-- One initial pop, one loop guard, one repeated-body pop: exactly three
    physical control sites in addition to the opaque numerical row body. -/
theorem outer_site_count :
    StructuredCalls.size outer = StructuredCalls.size row + 3 := by
  change 1 + ((StructuredCalls.size row + 1) + 1) =
    StructuredCalls.size row + 3
  omega

/-- The readout's physical label count is a *symbolic* formula: the runtime
    iteration counts are not part of this static expression. This does not
    assert that the opaque row's code can already be exported. -/
theorem readout_label_count :
    StructuredCalls.size command + 1 =
      StructuredCalls.size prepare +
        (StructuredCalls.size row + 3 + StructuredCalls.size finish) + 1 := by
  change StructuredCalls.size prepare +
      (StructuredCalls.size outer + StructuredCalls.size finish) + 1 =
    StructuredCalls.size prepare +
      (StructuredCalls.size row + 3 + StructuredCalls.size finish) + 1
  rw [outer_site_count]

/-- For every *source* instruction site, the original compiled readout uses
    precisely the corresponding source-defined instruction with the original
    site address and continuation. No finite enumeration is required. -/
theorem instruction_at_source_site (q : StructuredCalls.Site command) :
    program.code (StructuredCalls.siteAddress command q) =
      StructuredCalls.code command
        (StructuredCalls.siteAddress command)
        (StructuredCalls.exitAddress command) q := by
  exact StructuredCalls.compiled_site command (15 : Fin 40) (0 : Fin 40) q

/-- The exit is also checked. A site-only correspondence would miss it. -/
theorem instruction_at_source_exit :
    program.code (StructuredCalls.exitAddress command) = BitProgram.Instr.halt := by
  exact StructuredCalls.compiled_exit command (15 : Fin 40) (0 : Fin 40)

/-- Every source-level execution of the original readout factors through the
    exact prepare/outer/finish boundary, with two intermediate states and
    additive instruction costs. The converse composes those observations.
    The row's numerical correctness remains a separate theorem obligation. -/
theorem eval_iff_components (n : ℕ)
    (a b : StructuredCalls.State 8 40) :
    StructuredCalls.Eval command n a b ↔
      ∃ (np no nf : ℕ) (prepared iterated : StructuredCalls.State 8 40),
        n = np + (no + nf) ∧
        StructuredCalls.Eval prepare np a prepared ∧
        StructuredCalls.Eval outer no prepared iterated ∧
        StructuredCalls.Eval finish nf iterated b := by
  constructor
  · intro h
    change StructuredCalls.Eval (.seq prepare (.seq outer finish)) n a b at h
    cases h with
    | seq hp hrest =>
      cases hrest with
      | seq ho hf =>
        exact ⟨_, _, _, _, _, rfl, hp, ho, hf⟩
  · rintro ⟨np, no, nf, prepared, iterated, hn, hp, ho, hf⟩
    subst n
    change StructuredCalls.Eval
      (.seq prepare (.seq outer finish)) (np + (no + nf)) a b
    exact StructuredCalls.Eval.seq hp (StructuredCalls.Eval.seq ho hf)

end OAI.Algorithms.SubexponentialSAT.ReadoutShell
