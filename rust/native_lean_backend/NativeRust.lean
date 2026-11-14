import Lean

namespace NativeRust

/-- A borrowed, in-process Lean.IR.Decl passed directly to Rust.
    Rust returns `OK\n<source>` or `ERROR\n<reason>`; no serialized IR. -/
@[extern "rs_emit_ir"] opaque emit (decl : @& Lean.IR.Decl) (rustName : @& String) : String

/-- Emit a closed executable dependency graph in-process (no JSON IR). -/
@[extern "rs_emit_ir_module"] opaque emitModule
  (decls : @& Array Lean.IR.Decl) (root : @& String) (rustName : @& String) : String

/-- Emit several public roots through one shared, deduplicated IR closure. -/
@[extern "rs_emit_ir_module_many"] opaque emitModuleMany
  (decls : @& Array Lean.IR.Decl) (roots : @& Array String) : String


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


/-- Read direct calls out of the *elaborated compiler IR*, not Lean syntax.
    A recognized body's dependencies are scanned in Lean, including IR imported
    from precompiled modules. Rust independently checks the resulting closure. -/
private partial def callsInBody : Lean.IR.FnBody → Array Lean.Name
  | .vdecl _ _ (.fap f _) tail => #[f] ++ callsInBody tail
  | .vdecl _ _ (.pap f _) tail => #[f] ++ callsInBody tail
  | .vdecl _ _ _ tail => callsInBody tail
  | .case _ _ _ alts => alts.foldl (fun acc alt => acc ++ callsInBody alt.body) #[]
  | .jdecl _ _ value tail => callsInBody value ++ callsInBody tail
  | .set _ _ _ tail => callsInBody tail
  | .setTag _ _ tail => callsInBody tail
  | .uset _ _ _ tail => callsInBody tail
  | .sset _ _ _ _ _ tail => callsInBody tail
  | .inc _ _ _ _ tail => callsInBody tail
  | .dec _ _ _ _ tail => callsInBody tail
  | .del _ tail => callsInBody tail
  | _ => #[]

/-- Compile the root and inspect the exact in-process IR dependency closure.
    Definitions in already-imported modules are retrieved by IR.findDecl. A
    missing/unsupported symbol remains a hard error in the Rust backend. -/
private def gatherClosure (roots : Array Lean.Name) : Lean.CoreM (Array Lean.IR.Decl) := do
  if roots.isEmpty then throwError "expected at least one Lean declaration"
  Lean.Compiler.compile roots
  let mut queue := roots
  let mut seen : Std.HashSet Lean.Name := {}
  let mut decls : Array Lean.IR.Decl := #[]
  while !queue.isEmpty do
    let name := queue.back!
    queue := queue.pop
    if seen.contains name then continue
    seen := seen.insert name
    if seen.size > 2048 then
      throwError "Rust native dependency closure exceeded 2048 names"
    if let some decl ← Lean.IR.findDecl name then
      if let some blame := decl.getInfo.sorryDep? then
        throwError "Rust native backend refused {name}: dependency on sorry axiom {blame}"
      -- The native backend implements these *exact* Lean runtime externs,
      -- validating their arity, IR types and erased argument positions.
      -- Do not inject opaque extern declarations into the compiled closure.
      if let .extern .. := decl then
        if #["Array.mkEmpty", "Array.push", "Array.size", "Array.getInternal", "Array.getInternalBorrowed", "Array.set!"].contains name.toString then
          continue
      decls := decls.push decl
      if let .fdecl _ _ _ body _ := decl then
        queue := queue ++ callsInBody body
  return decls

def compileClosure (root : Lean.Name) (rustName : String) : Lean.CoreM String := do
  let decls ← gatherClosure #[root]
  let report := emitModule decls root.toString rustName
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused {root}: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned an invalid closure response for {root}"

/-- Produce a complete standalone Rust library, sharing any overlapping roots. -/
def compileMany (roots : Array Lean.Name) : Lean.CoreM String := do
  let decls ← gatherClosure roots
  let report := emitModuleMany decls (roots.map Lean.Name.toString)
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused compilation: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned invalid multi-root response"

/-- Publish a complete, new Cargo package by renaming a staging directory.
    We never overwrite an existing destination or publish a partial crate. -/
def publishPackage (destination : System.FilePath) (source : String) : IO Unit := do
  if ← destination.pathExists then
    throw <| IO.userError s!"refusing to overwrite existing Cargo package: {destination}"
  let temp ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (temp / "src")
    IO.FS.writeFile (temp / "Cargo.toml")
      "[package]\nname = \"lean_generated\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\npath = \"src/lib.rs\"\n\n[workspace]\n"
    IO.FS.writeFile (temp / "src" / "lib.rs") source
    IO.FS.rename temp destination
  catch err =>
    try IO.FS.removeDirAll temp catch _ => pure ()
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

syntax (name := nativeRustClosureCmd) "#native_rust_closure " ident " as " str " to " str : command

@[command_elab nativeRustClosureCmd]
def elabNativeRustClosureCmd : CommandElab := fun stx => do
  match stx with
  | `(#native_rust_closure $root:ident as $rustName:str to $outFile:str) =>
    let code ← liftCoreM <| NativeRust.compileClosure root.getId rustName.getString
    liftIO <| NativeRust.writeAtomically outFile.getString code
    logInfo m!"Native Rust backend emitted dependency closure for {root.getId}"
  | _ => throwUnsupportedSyntax

syntax (name := nativeRustPackageCmd) "#native_rust_package " "[" ident,* "]" " to " str : command

@[command_elab nativeRustPackageCmd]
def elabNativeRustPackageCmd : CommandElab := fun stx => do
  match stx with
  | `(#native_rust_package [$roots:ident,*] to $outDir:str) =>
    let names := roots.getElems.map (·.getId)
    let code ← liftCoreM <| NativeRust.compileMany names
    liftIO <| NativeRust.publishPackage outDir.getString code
    logInfo m!"Native Rust backend emitted standalone Cargo library ({names.size} public roots)"
  | _ => throwUnsupportedSyntax
