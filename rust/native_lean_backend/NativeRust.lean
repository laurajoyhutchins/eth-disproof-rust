import Lean

namespace NativeRust

/-- Stable, machine-readable refusal for failures before native IR reaches Rust. -/
private def refusalMessage (decl : Lean.Name) (construct reason : String) : String :=
  "Rust native backend refused " ++ decl.toString ++ ": " ++
    (Lean.Json.mkObj [
      ("status", .str "refused"),
      ("declaration", .str decl.toString),
      ("construct", .str construct),
      ("reason", .str reason)
    ]).compress

/-- A borrowed, in-process Lean.IR.Decl passed directly to Rust.
    Rust returns `OK\n<source>` or `ERROR\n<reason>`; no serialized IR. -/
@[extern "rs_emit_ir"] opaque emit (decl : @& Lean.IR.Decl) (rustName : @& String) : String

/-- Emit a closed executable dependency graph in-process (no JSON IR). -/
@[extern "rs_emit_ir_module"] opaque emitModule
  (decls : @& Array Lean.IR.Decl) (root : @& Lean.Name) (rustName : @& String) : String

/-- Emit several public roots through one shared, deduplicated IR closure. -/
@[extern "rs_emit_ir_module_many"] opaque emitModuleMany
  (decls : @& Array Lean.IR.Decl) (roots : @& Array Lean.Name) : String


/-- Compile one executable declaration with the pinned Lean compiler and emit Rust.
    Refuses declarations missing IR, or outside the backend's strict subset. -/
def compile (root : Lean.Name) (rustName : String) : Lean.CoreM String := do
  -- Existing imported .olean IR is already the compiler's executable artifact.
  -- Only compile roots missing IR; never substitute an alternative algorithm.
  if (← Lean.IR.findDecl root).isNone then
    Lean.Compiler.compile #[root]
  let some decl ← Lean.IR.findDecl root
    | throwError "{refusalMessage root "CompilerIR" "no compiler IR (possibly noncomputable)"}"
  if let some blame := decl.getInfo.sorryDep? then
    throwError "{refusalMessage root "SorryAxiom" s!"dependency on sorry axiom {blame}"}"
  let report := emit decl rustName
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused {root}: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned an invalid response for {root}"

/-- Output publication remains same-process via a pinned Rust FFI entrypoint.
    Its sibling stage, relative path check and refusal semantics are enforced
    by the Rust publisher; no partial code is accepted after an error. -/
@[extern "rs_publish_source"] opaque publishSource
  (dst : @& String) (code : @& String) : String

def writeAtomically (dst : System.FilePath) (code : String) : IO Unit := do
  let report := publishSource dst.toString code
  if report.startsWith "OK\n" then
    return
  else if report.startsWith "ERROR\n" then
    throw <| IO.userError s!"Rust native publisher refused {dst}: {(report.drop 6).toString}"
  else
    throw <| IO.userError s!"Rust native publisher returned an invalid response for {dst}"

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
  -- Preserve already-imported executable compiler IR; compile only missing
  -- roots. The transitive closure is inspected and validated below.
  let mut missing : Array Lean.Name := #[]
  for root in roots do
    if (← Lean.IR.findDecl root).isNone then
      missing := missing.push root
  unless missing.isEmpty do
    Lean.Compiler.compile missing
  let mut queue := roots
  let mut seen : Std.HashSet Lean.Name := {}
  let mut decls : Array Lean.IR.Decl := #[]
  while !queue.isEmpty do
    let name := queue.back!
    queue := queue.pop
    if seen.contains name then continue
    seen := seen.insert name
    if seen.size > 2048 then
      throwError "{refusalMessage name "ResourceLimit" "native dependency closure exceeded 2048 names"}"
    if let some decl ← Lean.IR.findDecl name then
      if let some blame := decl.getInfo.sorryDep? then
        throwError "{refusalMessage name "SorryAxiom" s!"dependency on sorry axiom {blame}"}"
      decls := decls.push decl
      if let .fdecl _ _ _ body _ := decl then
        queue := queue ++ callsInBody body
  return decls

def compileClosure (root : Lean.Name) (rustName : String) : Lean.CoreM String := do
  let decls ← gatherClosure #[root]
  let report := emitModule decls root rustName
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused {root}: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned an invalid closure response for {root}"

/-- Produce a complete standalone Rust library, sharing any overlapping roots. -/
def compileMany (roots : Array Lean.Name) : Lean.CoreM String := do
  let decls ← gatherClosure roots
  let report := emitModuleMany decls roots
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused compilation: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned invalid multi-root response"

/-- A complete binary needs a zero-argument scalar result. An arbitrary
    function is not a CLI entry point, so refuse rather than invent arguments. -/
def compileExecutable (root : Lean.Name) : Lean.CoreM String := do
  if (← Lean.IR.findDecl root).isNone then
    Lean.Compiler.compile #[root]
  let some (.fdecl _ params result _ _) ← Lean.IR.findDecl root
    | throwError "Rust native executable refused {root}: no executable function IR"
  unless params.isEmpty do
    throwError "Rust native executable refused {root}: entry requires zero arguments"
  unless result == .uint8 || result == .uint16 || result == .uint32 ||
         result == .uint64 || result == .usize || result == .float do
    throwError "Rust native executable refused {root}: entry requires a printable scalar return"
  let code ← compileClosure root "lean_result"
  return code ++ "\nfn main() { println!(\"{}\", lean_result()); }\n"

/-- Publish a complete, new Cargo package by renaming a staging directory.
    We never overwrite an existing destination or publish a partial crate. -/
def publishTarget (destination : System.FilePath) (source : String)
    (binary : Bool) : IO Unit := do
  if ← destination.pathExists then
    throw <| IO.userError s!"refusing to overwrite existing Cargo package: {destination}"
  let kind := if binary then "[bin]" else "lib"
  let filename := if binary then "main.rs" else "lib.rs"
  let manifest := "[package]\nname = \"lean_generated\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[" ++
    kind ++ "]\nname = \"lean_generated\"\npath = \"src/" ++ filename ++ "\"\n\n[workspace]\n"
  let temp ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (temp / "src")
    IO.FS.writeFile (temp / "Cargo.toml") manifest
    IO.FS.writeFile (temp / "src" / filename) source
    IO.FS.rename temp destination
  catch err =>
    try IO.FS.removeDirAll temp catch _ => pure ()
    throw err

def publishPackage (destination : System.FilePath) (source : String) : IO Unit :=
  publishTarget destination source false

def publishExecutable (destination : System.FilePath) (source : String) : IO Unit :=
  publishTarget destination source true

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

syntax (name := nativeRustBinaryCmd) "#native_rust_binary " ident " to " str : command

@[command_elab nativeRustBinaryCmd]
def elabNativeRustBinaryCmd : CommandElab := fun stx => do
  match stx with
  | `(#native_rust_binary $root:ident to $outDir:str) =>
    let code ← liftCoreM <| NativeRust.compileExecutable root.getId
    liftIO <| NativeRust.publishExecutable outDir.getString code
    logInfo m!"Native Rust backend emitted standalone Cargo binary for {root.getId}"
  | _ => throwUnsupportedSyntax
