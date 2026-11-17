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
  if s.endsWith ".Atom.set" then return some "atom-set"
  if s.endsWith ".Atom.copy" then return some "atom-copy"
  if s.endsWith ".Atom.bnot" then return some "atom-not"
  if s.endsWith ".Atom.band" then return some "atom-and"
  if s.endsWith ".Atom.bor" then return some "atom-or"
  if s.endsWith ".Atom.bxor" then return some "atom-xor"
  if s.endsWith ".Atom.push" then return some "atom-push"
  if s.endsWith ".Atom.peek" then return some "atom-peek"
  if s.endsWith ".Atom.pop" then return some "atom-pop"
  return none

/--
Static operand roles from original StructuredProgram.Atom constructors.
Indices are positions in the elaborated application (including r/s binders).
They are NOT evaluated numeric ports or dynamic state-dependency traces.
-/
def operandEffects (name : Name) : Json := Id.run do
  let s := name.toString
  let mut rr : Array Nat := #[]
  let mut rw : Array Nat := #[]
  let mut sr : Array Nat := #[]
  let mut sw : Array Nat := #[]
  if s.endsWith ".Atom.set" then rw := #[2]
  if s.endsWith ".Atom.copy" || s.endsWith ".Atom.bnot" then
    rr := #[3]
    rw := #[2]
  if s.endsWith ".Atom.band" || s.endsWith ".Atom.bor" ||
      s.endsWith ".Atom.bxor" then
    rr := #[3, 4]
    rw := #[2]
  if s.endsWith ".Atom.push" then
    rr := #[3]
    sw := #[2]
  if s.endsWith ".Atom.peek" then
    sr := #[2]
    rw := #[3, 4]
  if s.endsWith ".Atom.pop" then
    sr := #[2]
    sw := #[2]
    rw := #[3, 4]
  if s.endsWith ".Cmd.while" || s.endsWith ".Cmd.ite" then
    rr := #[2]
  return Json.mkObj [
    ("reg_reads_arg_positions", toJson rr),
    ("reg_writes_arg_positions", toJson rw),
    ("stack_reads_arg_positions", toJson sr),
    ("stack_writes_arg_positions", toJson sw)]

def appHead (e : Expr) : Json :=
  match e.getAppFn with
  | .const n _ => toJson n.toString
  | _ => Json.null

/-- Inspect expression nodes without reduction. Application spines count once. -/
partial def scanOps (e : Expr) (path : String) (initial : Array Json) : Array Json := Id.run do
  let mut out := initial
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
          ("argument_heads", toJson (args.map appHead)),
          ("operand_effects", operandEffects n)])
    | head =>
      -- Applied lambdas and higher-order heads can contain real operators too.
      out := scanOps head s!"{path}.fn" out
    for h in [:args.size] do
      out := scanOps args[h]! s!"{path}.{h}" out
  else
    match e with
    | .lam _ type body _ =>
      out := scanOps type s!"{path}.type" out
      out := scanOps body s!"{path}.body" out
    | .forallE _ type body _ =>
      out := scanOps type s!"{path}.type" out
      out := scanOps body s!"{path}.body" out
    | .letE _ type value body _ =>
      out := scanOps type s!"{path}.type" out
      out := scanOps value s!"{path}.value" out
      out := scanOps body s!"{path}.body" out
    | .proj _ _ value =>
      out := scanOps value s!"{path}.project" out
    | .mdata _ value =>
      out := scanOps value s!"{path}.metadata" out
    | _ => pure ()
  return out

def collectOps (e : Expr) (path : String) : Array Json :=
  scanOps e path #[]

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
