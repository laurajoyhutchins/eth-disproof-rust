import Lean

/-!
Capture Lean 4.34.1's actual final impure LCNF through the existing
process-local compiler environment. No new compiler pass or alternate emitter.

Lean.Compiler.LCNF.Pass.saveImpure already persists final declarations in
LCNF.impureExt. Imported, previously compiled declarations do not have a
process-local impure body and must be reported as unavailable.
-/

namespace NativeRust.LCNFCapture

open Lean Compiler LCNF

/-- Produce diagnostic evidence for a locally compiled executable declaration.
    Captures only final impure LCNF, never recreates it from Lean.IR. -/
meta def report (root : Name) : CoreM Json := do
  if (← Lean.IR.findDecl root).isNone then
    Lean.Compiler.compile #[root]
  let some decl ← getLocalImpureDecl? root
    | throwError "Final impure LCNF unavailable locally for {root}; imported IR alone is insufficient"
  unless (← Lean.IR.findDecl root).isSome do
    throwError "Lean compiler IR unavailable for saved impure declaration {root}"
  let formatted ← ppDecl' decl .impure
  return Json.mkObj [
    ("name", .str root.toString),
    ("phase", .str "impure"),
    ("source", .str "Lean.Compiler.LCNF.getLocalImpureDecl?"),
    ("lcnf_size", toJson decl.size),
    ("lcnf", .str (formatted.pretty 100))
  ]

end NativeRust.LCNFCapture
