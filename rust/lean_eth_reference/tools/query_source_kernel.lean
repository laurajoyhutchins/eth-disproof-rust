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

/-!
A *partial* source-to-IR projection. The only admitted constructor here is
the original StructuredCalls.Cmd.seq, which has the same node/child names as
the canonical Rust Command::Seq protocol. A closed named source definition
is preserved as an unresolved reference, never replaced with a surrogate
operation or treated as an executable leaf. No Meta whnf or evaluator.
-/
private partial def sourceCommandPrefix (env : Environment) (value : Expr)
    (fuel : Nat) (inlineTargets : Array String) : IO Json := do
  if fuel == 0 then
    throw <| IO.userError "original command prefix exceeds finite structural depth"
  match value with
  | .mdata _ nested =>
    sourceCommandPrefix env nested (fuel - 1) inlineTargets
  | _ =>
    match value.getAppFn with
    | .const symbol _ =>
      let args := value.getAppArgs
      if symbol == qualified "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq" then
        if args.size != 4 then
          throw <| IO.userError "original source Cmd.seq application arity differs"
        let first ← sourceCommandPrefix env args[2]! (fuel - 1) inlineTargets
        let second ← sourceCommandPrefix env args[3]! (fuel - 1) inlineTargets
        return Json.mkObj [
          ("kind", toJson "seq"), ("first", first), ("second", second)
        ]
      if args.isEmpty then
        match env.find? symbol with
        | some (.defnInfo info) =>
          if inlineTargets.contains symbol.toString then
            -- Expand only this explicitly requested source definition. Its
            -- children remain named obligations, avoiding unbounded unfolding.
            return (← sourceCommandPrefix env info.value (fuel - 1) #[])
          return Json.mkObj [
            ("kind", toJson "unresolved"),
            ("declaration", toJson symbol.toString),
            ("source_kind", toJson "definition")
          ]
        | some info =>
          throw <| IO.userError s!"source command leaf is not a definition: {symbol} ({kindOf info})"
        | none =>
          throw <| IO.userError s!"missing original command leaf: {symbol}"
      -- Preserve the head of an applied source definition as an explicit
      -- unresolved obligation. Its arguments, including finite port maps,
      -- are NOT lowered, discarded into executable code, or assumed erased.
      match env.find? symbol with
      | some (.defnInfo _) =>
        return Json.mkObj [
          ("kind", toJson "unresolved"),
          ("declaration", toJson symbol.toString),
          ("source_kind", toJson "application")
        ]
      | some info =>
        throw <| IO.userError s!"unsupported applied source declaration: {symbol} ({kindOf info})"
      | none =>
        throw <| IO.userError s!"missing applied original source definition: {symbol}"
    | _ =>
      throw <| IO.userError "original command prefix is not a constructor or closed source definition"

/-!
Inspect the exact *applied* original liftCommand without Meta reduction. In
particular, capture argument order, heads and bounded constant references.
Nothing in this diagnostic invents Fin port maps or emits executable code.
-/
private def headIdentity (value : Expr) : String :=
  match value.getAppFn with
  | .const name _ => name.toString
  | .lit _ => "#literal"
  | .lam .. => "#lambda"
  | .bvar _ => "#bound"
  | .proj .. => "#projection"
  | _ => "#other"

private def inspectSourceLift (env : Environment) : IO Json := do
  let commandName := qualified
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command"
  let some (.defnInfo command) := env.find? commandName
    | throw <| IO.userError "original reconstruction command source absent"
  unless headIdentity command.value ==
      "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq" do
    throw <| IO.userError "original reconstruction command is not a sequence"
  let commandArgs := command.value.getAppArgs
  unless commandArgs.size == 4 do
    throw <| IO.userError "original reconstruction sequence arity changed"
  let lift := commandArgs[3]!
  let name := qualified "OAI.Algorithms.SubexponentialSAT.StructuredCalls.liftCommand"
  unless headIdentity lift == name.toString do
    throw <| IO.userError "original reconstruction lift identity changed"
  let args := lift.getAppArgs
  if args.size < 5 || args.size > 16 then
    throw <| IO.userError "original reconstruction lift argument bound changed"
  let mut items : Array Json := #[]
  for i in [:args.size] do
    let (symbols, nodes) ←
      match immediateSymbols args[i]! 256 with
      | .ok result => pure result
      | .error reason =>
        throw <| IO.userError s!"original lift argument {i}: {reason}"
    items := items.push <| Json.mkObj [
      ("index", toJson i),
      ("head", toJson (headIdentity args[i]!)),
      ("nodes", toJson nodes),
      ("symbols", toJson symbols)
    ]
  let some (.defnInfo liftDef) := env.find? name
    | throw <| IO.userError "original liftCommand is not a definition"
  let (bodySymbols, bodyNodes) ←
    match immediateSymbols liftDef.value 512 with
    | .ok result => pure result
    | .error reason => throw <| IO.userError s!"original liftCommand: {reason}"
  for required in #[
      "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.call",
      "OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram",
      "OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled"] do
    unless bodySymbols.contains required do
      throw <| IO.userError s!"original liftCommand no longer references {required}"
  return Json.mkObj [
    ("declaration", toJson name.toString),
    ("argument_count", toJson args.size),
    ("arguments", toJson items),
    ("definition_body_nodes", toJson bodyNodes),
    ("definition_body_symbols", toJson bodySymbols),
    ("lowered_to_executable_call", toJson false)
  ]

/-!
Lower only the pinned source's syntactically recognized Fin literals and
identity/castAdd maps. This produces an honest *partial* canonical Rust call
tree: the inner original coreCommand remains unresolved, and no executable
or Lean↔Rust proof is inferred. The bounds and names come from the imported
Lean Expr, not a source-text rewrite or a surrogate implementation.
-/
private def sourceNat (e : Expr) : Except String Nat :=
  match e with
  | .lit (.natVal n) => .ok n
  | _ =>
    if headIdentity e != "OfNat.ofNat" then
      .error "source Nat is not an original numeral"
    else
      let args := e.getAppArgs
      match args[1]? with
      | some (.lit (.natVal n)) => .ok n
      | _ => .error "source numeral has no literal numeric argument"

private def requiredNat (e : Expr) (label : String) : IO Nat :=
  match sourceNat e with
  | .ok n => pure n
  | .error reason => throw <| IO.userError s!"{label}: {reason}"

private def requiredFin (e : Expr) (bound : Nat) (label : String) : IO Nat := do
  unless headIdentity e == "OfNat.ofNat" do
    throw <| IO.userError s!"{label}: not an elaborated Fin numeral"
  let args := e.getAppArgs
  if args.size < 2 || headIdentity args[0]! != "Fin" then
    throw <| IO.userError s!"{label}: not a Fin type"
  let typeArgs := args[0]!.getAppArgs
  if typeArgs.isEmpty then
    throw <| IO.userError s!"{label}: missing Fin bound"
  let observedBound ← requiredNat typeArgs[0]! s!"{label} bound"
  unless observedBound == bound do
    throw <| IO.userError s!"{label}: Fin bound mismatches source machine"
  let n ← requiredNat e label
  unless n < bound do
    throw <| IO.userError s!"{label}: Fin port out of range"
  return n

private partial def stripSourceLambdas (value : Expr) (fuel : Nat) : IO Expr := do
  if fuel == 0 then
    throw <| IO.userError "source lift definition lambda budget exceeded"
  match value with
  | .lam _ _ body _ => stripSourceLambdas body (fuel - 1)
  | .mdata _ body => stripSourceLambdas body (fuel - 1)
  | _ => pure value

private def originalLiftCall (env : Environment) : IO Json := do
  let commandName := qualified
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command"
  let some (.defnInfo source) := env.find? commandName
    | throw <| IO.userError "original reconstruction command missing"
  unless headIdentity source.value ==
      "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq" do
    throw <| IO.userError "source reconstruction stopped sequencing"
  let rootArgs := source.value.getAppArgs
  unless rootArgs.size == 4 do
    throw <| IO.userError "source reconstruction sequencing arity changed"
  let lift := rootArgs[3]!
  let liftName := qualified "OAI.Algorithms.SubexponentialSAT.StructuredCalls.liftCommand"
  unless headIdentity lift == liftName.toString do
    throw <| IO.userError "source reconstruction lift head changed"
  let a := lift.getAppArgs
  unless a.size == 9 do
    throw <| IO.userError "source lift no longer has four implicit and five explicit arguments"
  let r ← requiredNat a[0]! "source inner register dimension"
  let s ← requiredNat a[1]! "source inner stack dimension"
  let R ← requiredNat a[2]! "source outer register dimension"
  let S ← requiredNat a[3]! "source outer stack dimension"
  if r == 0 || r > 256 || s == 0 || s > 4096 || R != r ||
      S > 4096 || S < s then
    throw <| IO.userError "source lift dimensions out of supported exact map bounds"
  let coreName := qualified
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.coreCommand"
  if headIdentity a[4]! != coreName.toString ||
      !a[4]!.getAppArgs.isEmpty then
    throw <| IO.userError "source lift inner command is not original closed coreCommand"
  let some (.defnInfo _) := env.find? coreName
    | throw <| IO.userError "original reconstruction core is not a source definition"
  let input ← requiredFin a[5]! s "source compiled input"
  let output ← requiredFin a[6]! s "source compiled output"
  unless headIdentity a[7]! == "id" do
    throw <| IO.userError "original source register lift is not identity"
  unless headIdentity a[8]! == "Fin.castAdd" do
    throw <| IO.userError "original source stack lift is not Fin.castAdd"
  let castArgs := a[8]!.getAppArgs
  unless castArgs.size == 2 do
    throw <| IO.userError "source Fin.castAdd argument arity changed"
  let castFrom ← requiredNat castArgs[0]! "source Fin.castAdd domain"
  let castExtra ← requiredNat castArgs[1]! "source Fin.castAdd added dimension"
  unless castFrom == s && s + castExtra == S do
    throw <| IO.userError "source Fin.castAdd does not match source/target stacks"
  let some (.defnInfo liftDef) := env.find? liftName
    | throw <| IO.userError "liftCommand definition missing"
  let liftBody ← stripSourceLambdas liftDef.value 16
  unless headIdentity liftBody ==
      "OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.call" do
    throw <| IO.userError "source liftCommand is no longer a call"
  let callArgs := liftBody.getAppArgs
  if callArgs.isEmpty then
    throw <| IO.userError "source call has no program argument"
  let p := callArgs.back!
  unless headIdentity p ==
      "OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram" do
    throw <| IO.userError "source call no longer uses ProgramLinking.liftProgram"
  let pArgs := p.getAppArgs
  if pArgs.size < 3 then
    throw <| IO.userError "source liftProgram lacks its program and maps"
  let inner := pArgs[pArgs.size-3]!
  unless headIdentity inner ==
      "OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled" do
    throw <| IO.userError "source liftProgram no longer wraps compiled"
  let core := Json.mkObj [
    ("kind", toJson "unresolved"),
    ("declaration", toJson coreName.toString),
    ("source_kind", toJson "definition")
  ]
  return Json.mkObj [
    ("kind", toJson "call"),
    ("program", Json.mkObj [
      ("kind", toJson "lift"),
      ("r", toJson R), ("s", toJson S),
      ("registers", toJson (List.range r)),
      ("stacks", toJson (List.range s)),
      ("source", Json.mkObj [
        ("kind", toJson "composed"),
        ("r", toJson r), ("s", toJson s),
        ("input", toJson input), ("output", toJson output),
        ("command", core)
      ])
    ])
  ]

private def fieldRequired (node : Json) (name : String) : IO Json :=
  match node.getObjVal? name with
  | .ok value => pure value
  | .error _ => throw <| IO.userError s!"missing original command IR field {name}"

private partial def replaceOriginalLift (node replacement : Json)
    (fuel : Nat) : IO (Json × Nat) := do
  if fuel == 0 then
    throw <| IO.userError "original command replacement exceeded finite depth"
  let kind := match node.getObjValAs? String "kind" with
    | .ok s => s
    | .error _ => "#invalid"
  if kind == "seq" then
    let (first, countFirst) ←
      replaceOriginalLift (← fieldRequired node "first") replacement (fuel - 1)
    let (second, countSecond) ←
      replaceOriginalLift (← fieldRequired node "second") replacement (fuel - 1)
    return (Json.mkObj [
      ("kind", toJson "seq"), ("first", first), ("second", second)
    ], countFirst + countSecond)
  if kind == "unresolved" then
    let decl := match node.getObjValAs? String "declaration" with
      | .ok s => s
      | .error _ => "#invalid"
    if decl ==
        "OAI.Algorithms.SubexponentialSAT.StructuredCalls.liftCommand" then
      let sourceKind := match node.getObjValAs? String "source_kind" with
        | .ok s => s
        | .error _ => "#invalid"
      unless sourceKind == "application" do
        throw <| IO.userError "original lift replacement is not an applied definition"
      return (replacement, 1)
    return (node, 0)
  throw <| IO.userError "unsupported original command node during bounded lift substitution"

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
  let commandIR ← sourceCommandPrefix env commandInfo.value 32 #[]
  -- The three immediate command dependencies are the only authorized
  -- one-step expansion targets. Each is looked up in the pinned Lean env.
  let inlinedNames : Array String := #[
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.prepareHigh",
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.nodes",
    "OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.command"
  ]
  for name in inlinedNames do
    unless commandSymbols.contains name do
      throw <| IO.userError s!"original command no longer references expected source definition: {name}"
  let expandedIR ← sourceCommandPrefix env commandInfo.value 64 inlinedNames
  let liftApplication ← inspectSourceLift env
  let liftCall ← originalLiftCall env
  let (callIR, liftUses) ← replaceOriginalLift expandedIR liftCall 64
  unless liftUses == 1 do
    throw <| IO.userError "original source command must contain one lift application"
  let (localGraph, externalEdges, externalTargets) ← localDeclarations env root
  let (externalBodies, secondTargets) ←
    inspectExternalDefinitions env externalTargets 32768 32768 true
  let (secondBodies, _) ←
    inspectExternalDefinitions env secondTargets 65536 65536 false
  return Json.mkObj [
    ("format", toJson "original-query-kernel-root-v8"),
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
    ("source_command_ir", commandIR),
    ("source_command_expanded_ir", expandedIR),
    ("source_lift_application", liftApplication),
    ("source_lift_call_ir", liftCall),
    ("source_command_call_ir", callIR),
    ("source_command_ir_resolved", toJson false),
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
