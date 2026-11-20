import OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-!
# Structural extensionality for physical BitProgram tables

Physical programs are equal when their input stack, output stack, entry
label, and instruction at every label agree. Both source-graph and framed
reader refinements use this same field-level argument.

This lemma concerns the Lean program representation, not a Rust decoder or
its machine execution.
-/

namespace ACC.BitProgramFields

open BitProgram

/-- Agreement of all physical program fields determines the whole program. -/
theorem eq_of_fields {r s l : ℕ} (p q : Program r s l)
    (hinput : p.inputStack = q.inputStack)
    (houtput : p.outputStack = q.outputStack)
    (hentry : p.entry = q.entry)
    (hcode : ∀ pc, p.code pc = q.code pc) : p = q := by
  cases p with
  | mk pi po pe pc =>
    cases q with
    | mk qi qo qe qc =>
      dsimp at hinput houtput hentry hcode
      cases hinput
      cases houtput
      cases hentry
      have htable : pc = qc := funext hcode
      cases htable
      rfl

#print axioms ACC.BitProgramFields.eq_of_fields

end ACC.BitProgramFields
