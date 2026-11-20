import ProbeP2.Extraction.Funs

/-!
# P2: source-derived mutable-vector effect and returned Result

This file is compiled inside the Aeneas-generated ProbeP2 Lean package.
It imports the *actual generated* function, never a handwritten replacement.

The refinement is conditional on a successful modelled Vec.push. It proves
the return/refusal value and post-state of the extracted P2 body, but does
NOT prove Rust allocator capacity, Aeneas model adequacy, or the production
ranked tracer (which is blocked separately).
-/

open Aeneas Aeneas.Std
open RustM
namespace ranked_source_proof_harness

/-- Independent functional specification of the Result part. -/
def p2ExpectedResult (value : Std.U64) (refuse : Bool) :
    core.result.Result Std.U64 Std.U8 :=
  if refuse then core.result.Result.Err 7#u8
  else core.result.Result.Ok value

/-- The genuine extracted p0 source implements the independent Result function. -/
theorem p0_extracted_result (value : Std.U64) (refuse : Bool) :
    borrow_return_probe.p0_result_only value refuse =
      ok (p2ExpectedResult value refuse) := by
  cases refuse <;>
    simp [borrow_return_probe.p0_result_only, p2ExpectedResult]

/--
The actual extracted p2 first executes the modelled vector push, then returns
the stored Result. Under successful push, the exact vector post-state and
refusal value match the independent specification.

This is a kernel theorem about an Aeneas-generated Lean function and its
modelled Vec operation. It is NOT an unconditional Rust source theorem.
-/
theorem p2_extracted_effect
    (events events' : alloc.vec.Vec Std.U64)
    (value : Std.U64) (refuse : Bool)
    (hpush : alloc.vec.Vec.push events value = ok events') :
    borrow_return_probe.p2_direct_result events value refuse =
      ok (p2ExpectedResult value refuse, events') := by
  simp [borrow_return_probe.p2_direct_result, p0_extracted_result, hpush]

#print axioms p0_extracted_result
#print axioms p2_extracted_effect

end ranked_source_proof_harness
