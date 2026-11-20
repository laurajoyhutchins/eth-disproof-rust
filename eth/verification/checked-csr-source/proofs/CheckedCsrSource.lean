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

#print axioms CheckedCsrSource.checked_csr_row.checked_row
#print axioms CheckedCsrSource.checked_row_source
