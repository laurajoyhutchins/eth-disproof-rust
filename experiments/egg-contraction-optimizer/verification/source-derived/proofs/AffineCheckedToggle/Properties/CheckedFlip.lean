import AffineCheckedToggle.Code.Funs

/-!
# Proof over Aeneas-extracted operational Rust

The implementation is generated from the exact Rust source file
`src/checked_toggle.rs` via Charon at a pinned toolchain version.
This proof must import the generated definition; it is not a proof about
a hand-written equivalent function. No axiom may replace the generated code.

Source-to-IR translation soundness and Aeneas's standard-library models
remain explicit trusted assumptions. This theorem is not a verification
of the entire certificate checker.
-/

namespace AffineCheckedToggle

open Aeneas Aeneas.Std Result

theorem checked_flip_calls_extracted_source
    (row : Slice Bool) (index : Std.Usize) :
    checked_flip row index = checked_toggle.flip_checked row index := by
  rfl

/-- First semantic obligation: compare the generated Rust function
with a pure, index-checked slice transformation under Aeneas's models. -/
def expectedFlip (row : Slice Bool) (index : Std.Usize) :
    Aeneas.Std.Result
      ((core.result.Result Unit Str) × (Slice Bool)) :=
  match row[index]? with
  | some bit =>
      .ok (.Ok (), row.set_opt index (some (!bit)))
  | none =>
      .ok (.Err (toStr "checker matrix column outside allocated row"), row)

theorem extracted_flip_matches_index_model
    (row : Slice Bool) (index : Std.Usize) :
    checked_flip row index = expectedFlip row index := by
  cases h : row[index]? with
  | none =>
      simp [checked_flip, checked_toggle.flip_checked, expectedFlip,
        core.slice.Slice.get_mut, core.slice.index.SliceIndexUsizeSlice,
        core.slice.index.Usize.get_mut, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        h]
  | some bit =>
      simp [checked_flip, checked_toggle.flip_checked, expectedFlip,
        core.slice.Slice.get_mut, core.slice.index.SliceIndexUsizeSlice,
        core.slice.index.Usize.get_mut, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch, h]

#print axioms AffineCheckedToggle.checked_flip_calls_extracted_source
#print axioms AffineCheckedToggle.extracted_flip_matches_index_model
