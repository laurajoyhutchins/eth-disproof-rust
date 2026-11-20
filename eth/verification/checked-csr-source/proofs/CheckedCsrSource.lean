import CheckedCsrSource.Code.Funs

/-!
Kernel typechecking of Charon/Aeneas-extracted signed CSR source.
The generated Funs.lean and Types.lean must be freshly regenerated and
hash-checked against the pinned source before this module is checked.

This checks the *generated code under explicit source-library models*;
no theorem yet refines the generated code to the independent mathematical
machineCheckedRow specification in Lean 4.34.1. Compiler/Charon/Aeneas
translation fidelity remains a separate trusted toolchain boundary.
-/

/-- The *generated Aeneas function*, not a handwritten decoder, must
refuse when its first checked offset-array lookup returns None.
The statement quantifies over every remaining input and all machine-word
row indices, including malformed arrays. This is only one refusal branch;
the complete generated-to-independent-model theorem remains open. -/
theorem CheckedCsrSource.generated_checked_row_missing_start_refuses
    (offsets columns : Aeneas.Std.Slice Aeneas.Std.Usize)
    (signs : Aeneas.Std.Slice Aeneas.Std.I8)
    (variables row : Aeneas.Std.Usize)
    (h :
      Aeneas.Std.core.slice.Slice.get
        (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice Aeneas.Std.Usize)
        offsets row = Aeneas.Std.Result.ok none) :
    CheckedCsrSource.checked_csr_row.checked_row
      offsets columns signs variables row = Aeneas.Std.Result.ok none := by
  simp [CheckedCsrSource.checked_csr_row.checked_row, h,
    Aeneas.Std.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    Aeneas.Std.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

#print axioms CheckedCsrSource.generated_checked_row_missing_start_refuses

#print axioms CheckedCsrSource.checked_csr_row.checked_row
#print axioms CheckedCsrSource.checked_row_source
