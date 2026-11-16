import Lean.Environment
import Lean.Data.Json

/-!
Kernel-environment-only probe for the original pinned QueryStream root.
No elaborator, no source replacement and no physical execution. Import the
compiled original module dynamically and do not load persistent environment
extensions. This is a bounded declaration-identity and direct-symbol inventory,
NOT the transitive computational closure or the source graph accepted by Rust.
-/
namespace QuerySourceKernel
open Lean

private def qualified (name : String) : Name :=
  (name.splitOn ".").foldl Name.str Name.anonymous

private def immediateSymbols (root : Expr) (maxNodes : Nat) :
    Except String (Array String × Nat) := Id.run do
  let mut pending : Array Expr := #[root]
  let mut seen : Std.HashSet Expr := {}
  let mut symbols : Array String := #[]
  let mut nodes := 0
  while !pending.isEmpty do
    let e := pending.back!
    pending := pending.pop
    if seen.contains e then continue
    if nodes >= maxNodes then
      return .error "kernel root expression exceeded finite node budget"
    seen := seen.insert e
    nodes := nodes + 1
    match e with
    | .const name _ =>
      let name := name.toString
      unless symbols.contains name do
        symbols := symbols.push name
    | .app f a =>
      pending := pending.push a |>.push f
    | .lam _ typ body _ =>
      pending := pending.push body |>.push typ
    | .forallE _ typ body _ =>
      pending := pending.push body |>.push typ
    | .letE _ typ value body _ =>
      pending := pending.push body |>.push value |>.push typ
    | .proj _ _ value =>
      pending := pending.push value
    | .mdata _ value =>
      pending := pending.push value
    | .fvar _ | .mvar _ =>
      return .error "source root contains a free/metavariable"
    | _ => pure ()
  return .ok (symbols, nodes)

private def inspect (env : Environment) (root compiled : Name) : IO Json := do
  let some (.defnInfo info) := env.find? root
    | throw <| IO.userError s!"original root is not a compiled definition: {root}"
  let head := info.value.getAppFn
  match head with
  | .const name _ =>
    unless name == compiled do
      throw <| IO.userError s!"original root compiler differs: {name}"
  | _ =>
    throw <| IO.userError s!"original root is not a source compiler application: {head}"
  let (symbols, nodes) ← match immediateSymbols info.value 512 with
    | .ok result => pure result
    | .error reason => throw <| IO.userError reason
  -- Classify immediate constants by the original kernel environment, not
  -- their names. A theorem is noted as a proof declaration; its erasure
  -- status in the transitive computational closure remains unproved.
  let mut kinds : Array Json := #[]
  for symbol in symbols do
    let name := qualified symbol
    let some info := env.find? name
      | throw <| IO.userError s!"original kernel symbol is missing: {symbol}"
    let kind := match info with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    kinds := kinds.push <| Json.mkObj [
      ("name", toJson symbol), ("kind", toJson kind)
    ]
  let compiledName := compiled.toString
  unless symbols.contains compiledName do
    throw <| IO.userError "source root does not reference the pinned compiler declaration"
  unless (env.find? compiled).isSome do
    throw <| IO.userError "pinned source compiler declaration missing in kernel environment"
  return Json.mkObj [
    ("format", toJson "original-query-kernel-root-v1"),
    ("status", toJson "SOURCE_ROOT_INVENTORIED_UNVERIFIED"),
    ("root", toJson root.toString),
    ("compiler", toJson compiledName),
    ("source_kind", toJson "definition"),
    ("immediate_symbols", toJson symbols),
    ("immediate_symbol_kinds", toJson kinds),
    ("expression_nodes", toJson nodes),
    ("root_app_arity", toJson info.value.getAppArgs.size),
    ("transitive_computational_closure", toJson false),
    ("rust_executable", toJson false),
    ("independent_lean_rust_parity", toJson false),
    ("counting_parity", toJson false),
    ("resource_correspondence", toJson false)
  ]

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [moduleName, rootName, compilerName] =>
    let moduleName := qualified moduleName
    let rootName := qualified rootName
    let compilerName := qualified compilerName
    IO.eprintln "QUERY_KERNEL_PHASE=begin-bounded-original-import"
    withImportModules #[{ module := moduleName }] {} fun env => do
      IO.eprintln "QUERY_KERNEL_PHASE=original-kernel-environment-loaded"
      let report ← inspect env rootName compilerName
      IO.println report.compress
  | _ =>
    throw <| IO.userError
      "usage: query_source_kernel.lean MODULE ROOT COMPILER; no substitute source accepted"

end QuerySourceKernel

unsafe def main (args : List String) : IO Unit :=
  QuerySourceKernel.main args
