import Lean

/-!
Read-only observation of the final ownership-lowered LCNF in Lean 4.34.1.

The compiler already stores final impure declarations in its local environment.
This pass records *only* which names crossed the real pass boundary. Reports
read those saved declarations from Lean itself, not from a parallel lowering
or invented source representation.
-/

namespace NativeRust.LCNFCapture

open Lean Compiler LCNF

private builtin_initialize observedExt : EnvExtension NameSet ←
  registerEnvExtension (mkInitial := pure {}) (asyncMode := .sync)

private meta def observePass : Pass where
  name := `nativeRustObserveImpure
  phase := .impure
  run decls := do
    for decl in decls do
      modifyEnv fun env => observedExt.modifyState env (·.insert decl.name)
    return decls

/-- Installed after Lean's final impure LCNF save; never changes compiler IR. -/
@[cpass] meta def installObserver : PassInstaller :=
  PassInstaller.installAfter .impure `saveImpure (fun _ => observePass)

/-- Report a declaration observed by this process, refusing imported or
    previously compiled declarations for which this pass did not run. -/
def report (root : Name) : CoreM Json := do
  if (← Lean.IR.findDecl root).isNone then
    Lean.Compiler.compile #[root]
  let observed := observedExt.getState (← getEnv)
  unless observed.contains root do
    throwError "LCNF observation missing for {root}; it was not compiled with the observer"
  let some decl ← getLocalImpureDecl? root
    | throwError "Final impure LCNF unavailable locally for {root}"
  unless (← Lean.IR.findDecl root).isSome do
    throwError "Lean compiler IR unavailable for observed declaration {root}"
  let formatted ← ppDecl' decl .impure
  return Json.mkObj [
    ("name", .str root.toString),
    ("phase", .str "impure"),
    ("hook", .str "after-saveImpure"),
    ("lcnf_size", toJson decl.size),
    ("lcnf", .str (formatted.pretty 100))
  ]

end NativeRust.LCNFCapture
