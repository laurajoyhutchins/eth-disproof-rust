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

/-!
Classify source constants from the imported kernel environment. The theorem
classification does NOT assert that a corresponding argument is erased in any
Rust representation or that transitive computational closure is complete.
-/
private def kindOf : ConstantInfo → String
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def classifySymbols (env : Environment) (symbols : Array String) :
    IO (Array Json) := do
  let mut kinds : Array Json := #[]
  for symbol in symbols do
    let name := qualified symbol
    let some info := env.find? name
      | throw <| IO.userError s!"original kernel symbol is missing: {symbol}"
    kinds := kinds.push <| Json.mkObj [
      ("name", toJson symbol), ("kind", toJson (kindOf info))
    ]
  return kinds

/-!
Bounded transitive discovery of *same-module* declarations only. External
source modules are unresolved edges; the result is not a computational closure.
Theorem and opaque/axiom bodies are never unfolded or treated as executable.
-/
private def localDeclarations (env : Environment) (root : Name) :
    IO (Array Json × Array Json × Array String) := do
  let localNamePrefix := "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram."
  let mut pending : Array String := #[root.toString]
  let mut seen : Std.HashSet String := {}
  let mut graph : Array Json := #[]
  let mut externalEdges : Array Json := #[]
  let mut externalTargets : Array String := #[]
  let mut totalNodes := 0
  while !pending.isEmpty do
    let symbol := pending.back!
    pending := pending.pop
    if seen.contains symbol then continue
    unless symbol.startsWith localNamePrefix do
      throw <| IO.userError s!"out-of-scope local declaration: {symbol}"
    if graph.size >= 32 then
      throw <| IO.userError "original local declaration budget exceeded"
    seen := seen.insert symbol
    let some info := env.find? (qualified symbol)
      | throw <| IO.userError s!"missing original local declaration: {symbol}"
    let (children, nodes) ← match info with
      | .defnInfo value =>
        match immediateSymbols value.value 2048 with
        | .ok result => pure result
        | .error reason => throw <| IO.userError s!"local declaration {symbol}: {reason}"
      | _ => pure (#[], 0)
    totalNodes := totalNodes + nodes
    if totalNodes > 8192 then
      throw <| IO.userError "original local source graph node budget exceeded"
    for child in children do
      if child.startsWith localNamePrefix then
        if !(seen.contains child) then
          pending := pending.push child
      else
        if externalEdges.size >= 8192 then
          throw <| IO.userError "original external declaration frontier budget exceeded"
        let some targetInfo := env.find? (qualified child)
          | throw <| IO.userError s!"missing original external declaration: {child}"
        externalEdges := externalEdges.push <| Json.mkObj [
          ("from", toJson symbol),
          ("to", toJson child),
          ("target_kind", toJson (kindOf targetInfo))
        ]
        if child.startsWith "OAI.Algorithms.SubexponentialSAT." &&
            kindOf targetInfo == "definition" &&
            !(externalTargets.contains child) then
          if externalTargets.size >= 32 then
            throw <| IO.userError "original external definition target budget exceeded"
          externalTargets := externalTargets.push child
    graph := graph.push <| Json.mkObj [
      ("name", toJson symbol),
      ("kind", toJson (kindOf info)),
      ("body_scanned", toJson (kindOf info == "definition")),
      ("expression_nodes", toJson nodes),
      ("immediate_symbols", toJson children)
    ]
  return (graph, externalEdges, externalTargets)

/-!
Expand exactly one source-derived layer beyond QueryStreamProgram. Targets
come only from observed external edges, never a hand-written allowlist.
A scanned body remains an inventory, not a compiled command. Oversized bodies
are named refusals with no invented or truncated symbol lists.
-/
private def inspectExternalDefinitions (env : Environment)
    (targets : Array String) (bodyBudget typeBudget : Nat) (collectNext : Bool) :
    IO (Array Json × Array String) := do
  if targets.size > 96 then
    throw <| IO.userError "original external definition target budget exceeded"
  let localNamePrefix := "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram."
  let mut bodies : Array Json := #[]
  let mut nextTargets : Array String := #[]
  let mut aggregateNodes := 0
  let mut aggregateTypeNodes := 0
  for symbol in targets do
    let some (.defnInfo info) := env.find? (qualified symbol)
      | throw <| IO.userError s!"original external definition missing: {symbol}"
    let (status, nodes, symbols) ←
      match immediateSymbols info.value 4096 with
      | .ok (children, count) =>
        if aggregateNodes + count > bodyBudget then
          pure ("aggregate_budget_refused", 0, #[])
        else
          aggregateNodes := aggregateNodes + count
          pure ("scanned", count, children)
      | .error reason =>
        if reason == "kernel root expression exceeded finite node budget" then
          pure ("node_budget_refused", 0, #[])
        else
          throw <| IO.userError s!"external definition {symbol}: {reason}"
    let kinds ← classifySymbols env symbols
    -- These are syntactic type-signature references, not an erasure proof.
    -- A term-body reference may itself occur in proof or type arguments.
    let (typeStatus, typeNodes, typeSymbols) ←
      match immediateSymbols info.type 4096 with
      | .ok (children, count) =>
        if aggregateTypeNodes + count > typeBudget then
          pure ("aggregate_budget_refused", 0, #[])
        else
          aggregateTypeNodes := aggregateTypeNodes + count
          pure ("scanned", count, children)
      | .error reason =>
        if reason == "kernel root expression exceeded finite node budget" then
          pure ("node_budget_refused", 0, #[])
        else
          throw <| IO.userError s!"external definition type {symbol}: {reason}"
    let typeKinds ← classifySymbols env typeSymbols
    if collectNext && status == "scanned" then
      for child in symbols do
        if child.startsWith "OAI.Algorithms.SubexponentialSAT." &&
            !(child.startsWith localNamePrefix) &&
            !(targets.contains child) && !(nextTargets.contains child) then
          let some childInfo := env.find? (qualified child)
            | throw <| IO.userError s!"missing original next-layer declaration: {child}"
          if kindOf childInfo == "definition" then
            if nextTargets.size >= 96 then
              throw <| IO.userError "original next-layer definition target budget exceeded"
            nextTargets := nextTargets.push child
    bodies := bodies.push <| Json.mkObj [
      ("name", toJson symbol),
      ("kind", toJson "definition"),
      ("status", toJson status),
      ("expression_nodes", toJson nodes),
      ("immediate_symbols", toJson symbols),
      ("immediate_symbol_kinds", toJson kinds),
      ("type_status", toJson typeStatus),
      ("type_expression_nodes", toJson typeNodes),
      ("type_immediate_symbols", toJson typeSymbols),
      ("type_symbol_kinds", toJson typeKinds)
    ]
  return (bodies, nextTargets)

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
  let kinds ← classifySymbols env symbols
  let compiledName := compiled.toString
  unless symbols.contains compiledName do
    throw <| IO.userError "source root does not reference the pinned compiler declaration"
  unless (env.find? compiled).isSome do
    throw <| IO.userError "pinned source compiler declaration missing in kernel environment"
  -- Follow exactly one source-defined computational edge from the original
  -- program to its command. Do not expand transitive dependencies or evaluate.
  let commandName := qualified
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command"
  unless symbols.contains commandName.toString do
    throw <| IO.userError "the original program does not reference QueryStreamProgram.command"
  let some (.defnInfo commandInfo) := env.find? commandName
    | throw <| IO.userError "the original QueryStream command is not a definition"
  let (commandSymbols, commandNodes) ←
    match immediateSymbols commandInfo.value 1024 with
    | .ok result => pure result
    | .error reason => throw <| IO.userError s!"original command: {reason}"
  let commandKinds ← classifySymbols env commandSymbols
  let (localGraph, externalEdges, externalTargets) ← localDeclarations env root
  let (externalBodies, secondTargets) ←
    inspectExternalDefinitions env externalTargets 32768 32768 true
  let (secondBodies, _) ←
    inspectExternalDefinitions env secondTargets 65536 65536 false
  return Json.mkObj [
    ("format", toJson "original-query-kernel-root-v4"),
    ("status", toJson "SOURCE_ROOT_INVENTORIED_UNVERIFIED"),
    ("root", toJson root.toString),
    ("compiler", toJson compiledName),
    ("source_kind", toJson "definition"),
    ("immediate_symbols", toJson symbols),
    ("immediate_symbol_kinds", toJson kinds),
    ("expression_nodes", toJson nodes),
    ("root_app_arity", toJson info.value.getAppArgs.size),
    ("command_name", toJson commandName.toString),
    ("command_expression_nodes", toJson commandNodes),
    ("command_immediate_symbols", toJson commandSymbols),
    ("command_symbol_kinds", toJson commandKinds),
    ("same_module_local_declarations", toJson localGraph),
    ("external_module_edges", toJson externalEdges),
    ("external_definition_bodies", toJson externalBodies),
    ("second_hop_definition_bodies", toJson secondBodies),
    ("external_module_edges_unresolved", toJson true),
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
