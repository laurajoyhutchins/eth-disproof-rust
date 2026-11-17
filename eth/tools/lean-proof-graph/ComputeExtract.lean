import Lean

open Lean

/-!
An elaborated-expression inventory of the original executable definitions.
This is NOT a compiler control-flow graph or an execution trace.

The exporter only follows actual constant references in definition bodies and
preserves each recognized control combinator's AST path and argument heads.
It does not unfold those combinators or assume their semantic equivalence.
All other source-package references are accounted for as declarations or
explicit non-definition boundaries. External references remain enumerated.
-/
namespace ComputeGraph

def isProject (source : String) (name : Name) : Bool :=
  let value := name.toString
  if source == "openai" then
    value.startsWith "OAI.Algorithms.SubexponentialSAT."
  else
    value.startsWith "ExplicitCost." ||
    value.startsWith "QueryMachines." ||
    value.startsWith "Groundwork." ||
    value.startsWith "PiecesCounted." ||
    value.startsWith "Printed." ||
    value.startsWith "CountedRecursion."

def opKind (name : Name) : Option String := Id.run do
  let s := name.toString
  if s.endsWith ".Cmd.seq" then return some "sequence"
  if s.endsWith ".Cmd.while" then return some "loop"
  if s.endsWith ".Cmd.ite" then return some "branch"
  if s.endsWith ".Cmd.call" then return some "call"
  if s.endsWith ".Cmd.base" then return some "base"
  if s.endsWith ".QueryMachine.bind" then return some "bind"
  if s.endsWith ".QueryMachine.ite" then return some "branch"
  if s.endsWith ".QueryMachine.sumRange" then return some "sum-range"
  if s.endsWith ".QueryMachine.foldRange" then return some "fold-range"
  if s.endsWith ".QueryMachine.prodRange" then return some "product-range"
  if s.endsWith ".QueryMachine.query" then return some "query"
  if s.endsWith ".QueryMachine.lift" then return some "lift"
  if s.endsWith ".QueryMachine.optBind" then return some "optional-bind"
  if s.endsWith ".QueryMachine.subst" then return some "substitution"
  if s.endsWith ".Tower.tower" then return some "recursion"
  return none

def appHead (e : Expr) : Json :=
  match e.getAppFn with
  | .const n _ => toJson n.toString
  | _ => Json.null

/-- Inspect expression nodes without reduction. Application spines count once. -/
partial def collectOps (e : Expr) (path : String) : Array Json := Id.run do
  let mut out := #[]
  let args := e.getAppArgs
  if !args.isEmpty then
    match e.getAppFn with
    | .const n _ =>
      if let some kind := opKind n then
        out := out.push (Json.mkObj [
          ("path", toJson path),
          ("operator", toJson n.toString),
          ("control_kind", toJson kind),
          ("arity", toJson args.size),
          ("argument_heads", toJson (args.map appHead))])
    | _ => pure ()
    for h in [:args.size] do
      out := out ++ collectOps args[h]! s!"{path}.{h}"
  else
    match e with
    | .lam _ type body _ =>
      out := out ++ collectOps type s!"{path}.type"
      out := out ++ collectOps body s!"{path}.body"
    | .forallE _ type body _ =>
      out := out ++ collectOps type s!"{path}.type"
      out := out ++ collectOps body s!"{path}.body"
    | .letE _ type value body _ =>
      out := out ++ collectOps type s!"{path}.type"
      out := out ++ collectOps value s!"{path}.value"
      out := out ++ collectOps body s!"{path}.body"
    | .proj _ _ value =>
      out := out ++ collectOps value s!"{path}.project"
    | .mdata _ value =>
      out := out ++ collectOps value s!"{path}.metadata"
    | _ => pure ()
  return out

def declarationKind (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem-boundary"
  | .axiomInfo _ => "axiom-boundary"
  | .inductInfo _ => "inductive-boundary"
  | .ctorInfo _ => "constructor-boundary"
  | .recInfo _ => "recursor-boundary"
  | .quotInfo _ => "quotient-boundary"

def executableBody? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo _ => ci.value? (allowOpaque := true)
  | .opaqueInfo _ => ci.value? (allowOpaque := true)
  | _ => none

def sortedRefs (e : Expr) : Array Name :=
  e.getUsedConstantsAsSet.toArray.qsort Name.lt

def run (source moduleName : String) (dest : System.FilePath)
    (roots : Array String) : IO Unit := do
  if source != "openai" && source != "anthropic" then
    throw (IO.userError "Expected original source openai or anthropic")
  if roots.isEmpty then
    throw (IO.userError "Expected at least one computational root")
  let env ← importModules #[{module := moduleName.toName}] {}
  let mut queue : Array Name := #[]
  let mut queued : NameSet := {}
  for root in roots do
    let name := root.toName
    if !isProject source name then
      throw (IO.userError s!"Root outside pinned computational project: {root}")
    if (env.checked.get.find? name).isNone then
      throw (IO.userError s!"Computational root absent from checked environment: {root}")
    if !queued.contains name then
      queue := queue.push name
      queued := queued.insert name
  let handle ← IO.FS.Handle.mk dest IO.FS.Mode.write
  handle.putStrLn (Json.mkObj [
    ("kind", toJson "manifest"),
    ("protocol", toJson "original-computational-expr-v1"),
    ("source", toJson source),
    ("module", toJson moduleName),
    ("roots", toJson roots),
    ("complete", toJson false),
    ("semantics", toJson "Elaborated expression references and operator syntax; not execution CFG")]).compress
  let mut index := 0
  let mut operators := 0
  while index < queue.size do
    let name := queue[index]!
    index := index + 1
    let some ci := env.checked.get.find? name
      | throw (IO.userError s!"Project reference absent: {name}")
    let moduleLabel := match env.getModuleIdxFor? name with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => "<unknown>"
    let body := executableBody? ci
    let refs := match body with
      | some b => sortedRefs b
      | none => #[]
    let projectRefs := refs.filter (isProject source)
    let externalRefs := refs.filter (fun n => !isProject source n)
    let ops := match body with
      | some b => collectOps b "0"
      | none => #[]
    operators := operators + ops.size
    handle.putStrLn (Json.mkObj [
      ("kind", toJson "declaration"),
      ("id", toJson name.toString),
      ("defining_module", toJson moduleLabel),
      ("declaration_kind", toJson (declarationKind ci)),
      ("body_available", toJson body.isSome),
      ("project_refs", toJson (projectRefs.map Name.toString)),
      ("external_refs", toJson (externalRefs.map Name.toString)),
      ("operators", toJson ops)]).compress
    for dep in projectRefs do
      if !queued.contains dep then
        unless (env.checked.get.find? dep).isSome do
          throw (IO.userError s!"Unresolved source-package constant: {dep}")
        queued := queued.insert dep
        queue := queue.push dep
    if index % 5000 == 0 then
      IO.eprintln s!"Computational source declarations: {index}; queued {queue.size}"
  handle.putStrLn (Json.mkObj [
    ("kind", toJson "complete"),
    ("nodes", toJson index),
    ("operators", toJson operators),
    ("roots", toJson roots)]).compress
  handle.flush
  IO.println s!"COMPUTATIONAL EXPRESSIONS: {index} declarations, {operators} operator occurrences"

end ComputeGraph

def main (args : List String) : IO Unit := do
  match args with
  | source :: moduleName :: destination :: roots =>
    ComputeGraph.run source moduleName destination roots.toArray
  | _ =>
    throw (IO.userError "Usage: lean --run ComputeExtract.lean openai|anthropic MODULE OUTPUT root...")
