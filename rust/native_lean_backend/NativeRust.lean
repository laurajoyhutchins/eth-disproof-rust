import Lean

namespace NativeRust

/-- A borrowed, in-process Lean.IR.Decl passed directly to Rust.
    Rust returns `OK\n<source>` or `ERROR\n<reason>`; no serialized IR. -/
@[extern "rs_emit_ir"] opaque emit (decl : @& Lean.IR.Decl) (rustName : @& String) : String

/-- Emit a closed executable dependency graph in-process (no JSON IR). -/
@[extern "rs_emit_ir_module"] opaque emitModule
  (decls : @& Array Lean.IR.Decl) (root : @& String) (rustName : @& String) : String


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

/-- The Rust publisher validates a workspace-relative .rs destination and writes
    to a unique sibling file before atomic rename. The caller can observe an
    explicit refusal but cannot receive a partially published artifact. -/
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
def compileClosure (root : Lean.Name) (rustName : String) : Lean.CoreM String := do
  Lean.Compiler.compile #[root]
  let mut queue := #[root]
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
      decls := decls.push decl
      if let .fdecl _ _ _ body _ := decl then
        queue := queue ++ callsInBody body
  let report := emitModule decls root.toString rustName
  if report.startsWith "OK\n" then
    return (report.drop 3).toString
  else if report.startsWith "ERROR\n" then
    throwError "Rust native backend refused {root}: {(report.drop 6).toString}"
  else
    throwError "Rust native backend returned an invalid closure response for {root}"

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
