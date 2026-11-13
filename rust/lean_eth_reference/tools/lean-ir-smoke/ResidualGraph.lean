import Lean

/-! A backend-independent, hash-consed residual of elaborated Lean core Expr.
This is a symbolic transport and refusal boundary, not an executable program. -/
namespace ResidualGraph
open Lean Meta Elab Command

private partial def encodeName : Name → Json
  | .anonymous => Json.mkObj [("tag", toJson "anonymous")]
  | .str parent value => Json.mkObj [("tag", toJson "str"), ("parent", encodeName parent), ("value", toJson value)]
  | .num parent value => Json.mkObj [("tag", toJson "num"), ("parent", encodeName parent), ("value", toJson value)]

private partial def encodeLevel : Level → Except String Json
  | .zero => pure <| Json.mkObj [("tag", toJson "zero")]
  | .succ inner => do
      pure <| Json.mkObj [("tag", toJson "succ"), ("inner", ← encodeLevel inner)]
  | .max left right => do
      pure <| Json.mkObj [("tag", toJson "max"), ("left", ← encodeLevel left), ("right", ← encodeLevel right)]
  | .imax left right => do
      pure <| Json.mkObj [("tag", toJson "imax"), ("left", ← encodeLevel left), ("right", ← encodeLevel right)]
  | .param n => pure <| Json.mkObj [("tag", toJson "param"), ("name", encodeName n)]
  | .mvar _ => .error "unassigned universe metavariable"

private def encodeBinder : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

structure Graph where
  nodes : Array Json := #[]
  seen : Std.HashMap Expr Nat := {}
  symbols : Array Name := #[]
  metadataDropped : Nat := 0

private def put (g : Graph) (e : Expr) (node : Json) : Graph × Nat :=
  let id := g.nodes.size
  ({ g with nodes := g.nodes.push node, seen := g.seen.insert e id }, id)

/-- Intern every core Expr by structural identity. No source command constructors
or ETH-specific names appear in this traversal. Metadata is semantically inert
and removed, but the original Expr is retained for definitional comparison. -/
private partial def intern (e : Expr) (g : Graph) (maxNodes fuel : Nat) : Except String (Graph × Nat) := do
  if let some id := g.seen[e]? then return (g, id)
  if fuel == 0 then throw "residual expression exceeds depth budget"
  if g.nodes.size >= maxNodes then throw "residual expression exceeds node budget"
  match e with
  | .mdata _ child =>
      let (g, id) ← intern child g maxNodes (fuel - 1)
      return ({g with seen := g.seen.insert e id, metadataDropped := g.metadataDropped + 1}, id)
  | .fvar _ => throw "free variable in a source declaration body"
  | .mvar _ => throw "unassigned expression metavariable"
  | .bvar index => return put g e <| Json.mkObj [("tag", toJson "bvar"), ("index", toJson index)]
  | .sort level => return put g e <| Json.mkObj [("tag", toJson "sort"), ("level", ← encodeLevel level)]
  | .const name levels =>
      let mut encoded := #[]
      for level in levels do
        encoded := encoded.push (← encodeLevel level)
      let g := if g.symbols.contains name then g else {g with symbols := g.symbols.push name}
      return put g e <| Json.mkObj [("tag", toJson "const"), ("name", encodeName name), ("levels", toJson encoded)]
  | .app fn arg =>
      let (g, f) ← intern fn g maxNodes (fuel - 1)
      let (g, a) ← intern arg g maxNodes (fuel - 1)
      return put g e <| Json.mkObj [("tag", toJson "app"), ("fn", toJson f), ("arg", toJson a)]
  | .lam name typ body info =>
      let (g, t) ← intern typ g maxNodes (fuel - 1)
      let (g, b) ← intern body g maxNodes (fuel - 1)
      return put g e <| Json.mkObj [("tag", toJson "lam"), ("name", encodeName name), ("binder", toJson (encodeBinder info)), ("type", toJson t), ("body", toJson b)]
  | .forallE name typ body info =>
      let (g, t) ← intern typ g maxNodes (fuel - 1)
      let (g, b) ← intern body g maxNodes (fuel - 1)
      return put g e <| Json.mkObj [("tag", toJson "forall"), ("name", encodeName name), ("binder", toJson (encodeBinder info)), ("type", toJson t), ("body", toJson b)]
  | .letE name typ value body nondep =>
      let (g, t) ← intern typ g maxNodes (fuel - 1)
      let (g, v) ← intern value g maxNodes (fuel - 1)
      let (g, b) ← intern body g maxNodes (fuel - 1)
      return put g e <| Json.mkObj [("tag", toJson "let"), ("name", encodeName name), ("type", toJson t), ("value", toJson v), ("body", toJson b), ("nondep", toJson nondep)]
  | .lit (.natVal value) =>
      return put g e <| Json.mkObj [("tag", toJson "nat"), ("value", toJson value)]
  | .lit (.strVal value) =>
      return put g e <| Json.mkObj [("tag", toJson "string"), ("value", toJson value)]
  | .proj name index value =>
      let (g, v) ← intern value g maxNodes (fuel - 1)
      return put g e <| Json.mkObj [("tag", toJson "proj"), ("name", encodeName name), ("index", toJson index), ("value", toJson v)]

private def auditSymbols (names : Array Name) : MetaM (Array String) := do
  let mut blockers := #[]
  for n in names do
    match (← getConstInfo n) with
    | .axiomInfo _ => blockers := blockers.push s!"axiom:{n}"
    | .opaqueInfo _ => blockers := blockers.push s!"opaque:{n}"
    | _ => pure ()
  return blockers

/-- Bounded syntactic β/ζ reduction only. This does not unroll a recursor,
inline arbitrary dependencies, or evaluate a noncomputable constant. All
reductions are checked for definitional equality before publication. -/
private partial def betaZetaOnce (e : Expr) : Option Expr :=
  match e with
  | .letE _ _ value body _ => some (body.instantiate1 value)
  | .app (.lam _ _ body _) arg => some (body.instantiate1 arg)
  | .app fn arg => (betaZetaOnce fn).map (fun reduced => mkApp reduced arg)
  | _ => none

private def reduceHead (e : Expr) (fuel : Nat := 16) : Expr × Nat := Id.run do
  let mut value := e
  let mut steps := 0
  for _ in [:fuel] do
    match betaZetaOnce value with
    | some next =>
        value := next
        steps := steps + 1
    | none => break
  return (value, steps)

/-- Retain both original and conservatively reduced roots in the graph.
The source declaration itself is unfolded once by getConstInfo. -/
private def residualize (name : Name) (maxNodes : Nat := 10000) : MetaM Json := do
  let original ← match (← getConstInfo name) with
    | .defnInfo info => pure info.value
    | _ => throwError m!"source root is not a definition: {name}"
  let typ ← inferType (mkConst name)
  let sourceTyp ← inferType original
  unless (← isDefEq typ sourceTyp) do
    throwError m!"declared type does not match elaborated body: {name}"
  if original.hasMVar || original.hasFVar then
    throwError "source declaration contains unresolved metavariables or free variables"
  -- Never use an unbounded whnf here. A closed Nat.rec with a billion
  -- iterations must survive as a handful of shared graph nodes.
  let (reduced, steps) := reduceHead original
  unless (← isDefEq original reduced) do
    throwError "syntactic residual is not definitionally equal to its source"
  let (graph, sourceId) ← match intern original {} maxNodes 4096 with
    | .ok result => pure result
    | .error message => throwError message
  let (graph, reducedId) ← match intern reduced graph maxNodes 4096 with
    | .ok result => pure result
    | .error message => throwError message
  let blockers ← auditSymbols graph.symbols
  if !blockers.isEmpty then
    throwError m!"source residual depends on non-executable declarations: {blockers}"
  return Json.mkObj [
    ("format", toJson "lean-core-expr-dag-v1"),
    ("status", toJson "residualized-unverified"),
    ("source", encodeName name),
    ("source_root", toJson sourceId),
    ("reduced_root", toJson reducedId),
    ("nodes", toJson graph.nodes),
    ("node_count", toJson graph.nodes.size),
    ("source_symbols", toJson (graph.symbols.map (·.toString))),
    ("metadata_dropped", toJson graph.metadataDropped),
    ("lean_defeq_checked", toJson true),
    ("beta_zeta_steps", toJson steps),
    ("rust_executable", toJson false),
    ("physical_refinement", toJson "not-established")
  ]

syntax (name := exportResidualGraph) "#export_residual_graph " ident : command
elab_rules : command
  | `(#export_residual_graph $root:ident) => do
    let result ← liftTermElabM <| residualize root.getId
    liftIO <| IO.println result.compress

end ResidualGraph
