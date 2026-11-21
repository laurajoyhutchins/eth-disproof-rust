import ProbeP12.Extraction.Funs

/-!
# Source-derived checked I128 recorder, exact outcome and vector post-state

This proof imports the *actual* Aeneas-generated p12 function, not a
handwritten stand-in. Theorems quantify over the Aeneas/CoreModels checked
addition and Vec.push models. Their successful-effect premises deliberately
exclude allocation failures, runtime compiler semantics, and the untranslated
production ranked arithmetic observer.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

namespace ranked_source_proof_harness

/--
The *actual extracted function* records the exact checked-addition option
before converting the option into a returned Result. If checked addition
evaluates to `observed` and the modelled vector push succeeds with
`events'`, the source-derived post-state is precisely `events'`, and the
return is the result of `Option.ok_or`.

This statement does not assume that `observed` is a success; None is
recorded before an overflow refusal result.
-/
theorem p12_extracted_checked_record
    (events events' : alloc.vec.Vec (core.option.Option Std.I128))
    (left right : Std.I128)
    (observed : core.option.Option Std.I128)
    (hchecked : core.num.I128.checked_add left right = ok observed)
    (hpush : alloc.vec.Vec.push events observed = ok events') :
    borrow_return_probe.p12_option_then_result events left right =
      (do
        let result ← core.option.Option.ok_or observed 9#u8
        ok (result, events')) := by
  simp [borrow_return_probe.p12_option_then_result, hchecked, hpush]

/-- On a checked-addition success, the event and return contain the same word. -/
theorem p12_extracted_success
    (events events' : alloc.vec.Vec (core.option.Option Std.I128))
    (left right value : Std.I128)
    (hchecked :
      core.num.I128.checked_add left right =
        ok (core.option.Option.Some value))
    (hpush :
      alloc.vec.Vec.push events (core.option.Option.Some value) = ok events') :
    borrow_return_probe.p12_option_then_result events left right =
      ok (core.result.Result.Ok value, events') := by
  simp [borrow_return_probe.p12_option_then_result,
    hchecked, hpush, core.option.Option.ok_or]

/-- On an overflow refusal, the trace still contains the None event. -/
theorem p12_extracted_refusal
    (events events' : alloc.vec.Vec (core.option.Option Std.I128))
    (left right : Std.I128)
    (hchecked :
      core.num.I128.checked_add left right =
        ok core.option.Option.None)
    (hpush :
      alloc.vec.Vec.push events core.option.Option.None = ok events') :
    borrow_return_probe.p12_option_then_result events left right =
      ok (core.result.Result.Err 9#u8, events') := by
  simp [borrow_return_probe.p12_option_then_result,
    hchecked, hpush, core.option.Option.ok_or]

#print axioms p12_extracted_checked_record
#print axioms p12_extracted_success
#print axioms p12_extracted_refusal

end ranked_source_proof_harness
