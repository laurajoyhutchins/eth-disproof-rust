import Lean

/-!
A bounded, source-elaborated inventory for the G2 ETH compiler gate.

This does NOT compile or execute the source program. It traverses dependencies
from elaborated definition bodies, never expands a Fin-indexed instruction table,
and reports which declarations have compiler IR *already observed in the imported
environment*. Absence of IR here is not proof that IR could never be generated.

Proof-only/type dependencies are not classified as executable requirements by
this syntactic scan. Axioms and opaque declarations are reported for further
computational-relevance review, not silently turned into Rust algorithms.
-/
namespace G2Inventory
open Lean Elab Command

private def bodyConstants (root : Expr) (maxExprs : Nat) : Except String (Array Name) := do
  let mut pending := #[root]
  let mut visited : Std.HashSet Expr := {}
  let mut named : Std.HashSet Name := {}
  let mut names : Array Name := #[]
  while !pending.isEmpty do
    let e := pending.back!
    pending := pending.pop
    if visited.contains e then continue
    visited := visited.insert e
    if visited.size > maxExprs then
      throw s!"expression traversal exceeded {maxExprs} nodes"
    match e with
    | .const n _ =>
        if !named.contains n then
          named := named.insert n
          names := names.push n
    | .app fn arg =>
        pending := (pending.push fn).push arg
    | .lam _ typ body _ | .forallE _ typ body _ =>
        pending := (pending.push typ).push body
    | .letE _ typ val body _ =>
        pending := ((pending.push typ).push val).push body
    | .mdata _ inner =>
        pending := pending.push inner
    | .proj _ _ inner =>
        pending := pending.push inner
    | .mvar _ => throw "unresolved expression metavariable in closure"
    | .fvar _ => throw "unexpected free variable in closed declaration"
    | .bvar _ | .sort _ | .lit _ => pure ()
  return names

/-- The output is an observation, not an executable-closure or proof certificate.
The limits prevent accidental unbounded expansion when importing ETH source. -/
def inventory (root : Name) (maxDecls : Nat := 4096)
    (maxExprsPerDecl : Nat := 100000) : CoreM Json := do
  let mut pending : Array Name := #[root]
  let mut seen : Std.HashSet Name := {}
  let mut declarations : Array Json := #[]
  let mut blockers : Array String := #[]
  let mut incomplete := false
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    if seen.size >= maxDecls then
      incomplete := true
      break
    seen := seen.insert n
    let info? := (← getEnv).find? n
    let ir := if (← Lean.IR.findDecl n).isSome then
      "observed-in-environment"
    else
      "not-observed"
    let mut kind := "missing"
    let mut deps : Array Name := #[]
    match info? with
    | none =>
        blockers := blockers.push s!"missing:{n}"
    | some (.defnInfo info) =>
        kind := "definition"
        deps ← match bodyConstants info.value maxExprsPerDecl with
          | .ok ds => pure ds
          | .error err => throwError m!"{n}: {err}"
    | some (.opaqueInfo _) =>
        kind := "opaque"
        blockers := blockers.push s!"opaque:{n}"
    | some (.axiomInfo _) =>
        kind := "axiom"
        blockers := blockers.push s!"axiom:{n}"
    | some (.thmInfo _) =>
        kind := "theorem"
    | some (.inductInfo _) =>
        kind := "inductive"
    | some (.ctorInfo _) =>
        kind := "constructor"
    | some (.recInfo _) =>
        kind := "recursor"
    | some _ =>
        kind := "other-unclassified"
        blockers := blockers.push s!"unclassified:{n}"
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson n.toString),
      ("kind", toJson kind),
      ("compiler_ir", toJson ir),
      ("body_dependencies", toJson (deps.map (·.toString)))
    ]
    pending := pending ++ deps
  return Json.mkObj [
    ("format", toJson "eth-original-closure-inventory-v1"),
    ("root", toJson root.toString),
    ("status", toJson (if incomplete then "bounded-incomplete" else "syntactic-closure-observed")),
    ("complete_syntactic_body_walk", toJson (!incomplete)),
    ("compiler_ir_scope", toJson "existing-imported-environment-only"),
    ("declaration_limit", toJson maxDecls),
    ("expression_limit_per_declaration", toJson maxExprsPerDecl),
    ("declaration_count", toJson declarations.size),
    ("declarations", toJson declarations),
    ("blockers_for_review", toJson blockers),
    ("computational_relevance_verified", toJson false),
    ("lean_rust_semantic_refinement", toJson "not-established"),
    ("physical_bitprogram_refinement", toJson "not-established"),
    ("eth_ready", toJson false)
  ]

end G2Inventory

open Lean Elab Command

syntax (name := ethClosureInventory) "#eth_closure_inventory " ident : command

@[command_elab ethClosureInventory]
def elabEthClosureInventory : CommandElab := fun stx => do
  match stx with
  | `(#eth_closure_inventory $root:ident) =>
      let report ← liftCoreM <| G2Inventory.inventory root.getId
      liftIO <| IO.println report.compress
  | _ => throwUnsupportedSyntax
