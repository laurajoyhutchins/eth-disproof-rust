import Lean

namespace NativeRust

/-- A borrowed, in-process Lean.IR.Decl passed directly to Rust.
    Rust returns `OK\n<source>` or `ERROR\n<reason>`; no serialized IR. -/
@[extern "rs_emit_ir"] opaque emit (decl : @& Lean.IR.Decl) (rustName : @& String) : String

/-- Compile one executable declaration with the pinned Lean compiler and emit Rust.
    Refuses declarations missing IR, or outside the backend's strict subset. -/
def compile (root : Lean.Name) (rustName : String) : Lean.CoreM String := do
  Lean.Compiler.compile #[root]
  let some decl ← Lean.IR.findDecl root
    | throwError "No compiler IR for {root} (possibly noncomputable)"
  if let some blame := decl.getInfo.sorryDep? then
    throwError "Rust native backend refused {root}: dependency on sorry axiom {blame}"
  let report := emit decl rustName
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused {root}: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned an invalid response for {root}"

/-- Do not publish partial Rust source on FFI failures or interrupted writes.
    The final rename is atomic when source and destination share a filesystem.
    Cross-filesystem moves refuse instead of falling back to a non-atomic copy. -/
def writeAtomically (dst : System.FilePath) (code : String) : IO Unit := do
  let (handle, temp) ← IO.FS.createTempFile
  try
    handle.putStr code
    handle.flush
    IO.FS.rename temp dst
  catch err =>
    try IO.FS.removeFile temp catch _ => pure ()
    throw err

end NativeRust

open Lean Elab Command

syntax (name := nativeRustCmd) "#native_rust " ident " as " str " to " str : command

@[command_elab nativeRustCmd]
def elabNativeRustCmd : CommandElab := fun stx => do
  match stx with
  | `(#native_rust $root:ident as $rustName:str to $outFile:str) =>
    let code ← liftCoreM <| NativeRust.compile root.getId rustName.getString
    liftIO <| NativeRust.writeAtomically outFile.getString code
    logInfo m!"Native Rust backend emitted {rustName.getString} from {root.getId}"
  | _ => throwUnsupportedSyntax
