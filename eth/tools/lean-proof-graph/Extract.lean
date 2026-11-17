import Lean

open Lean

namespace ProofGraph

/-- Distinguish the kernel's declaration classes, not syntactic Lean keywords. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

/-- Two different edges: one from the elaborated type, one from the actual body. -/
def refs (ci : ConstantInfo) : Array Name × Array Name := Id.run do
  let tys := ci.type.getUsedConstantsAsSet.toArray.qsort Name.lt
  let vals := match ci.value? (allowOpaque := true) with
    | some val => val.getUsedConstantsAsSet.toArray.qsort Name.lt
    | none => match ci with
      | .inductInfo v => v.ctors.toArray
      | .recInfo v => v.all.toArray
      | _ => #[]
  return (tys, vals)

def nodeJson (name : Name) (moduleName : String) (ci : ConstantInfo) : Json := Id.run do
  let (ty, body) := refs ci
  return Json.mkObj [
    ("id", toJson name.toString),
    ("module", toJson moduleName),
    ("kind", toJson (kindOf ci)),
    ("type_refs", toJson (ty.map Name.toString)),
    ("value_refs", toJson (body.map Name.toString)),
    ("has_body", toJson ((ci.value? (allowOpaque := true)).isSome))]

/--
Traverse every elaborated constant reachable from the exact requested roots.
Includes Mathlib, generated auxiliaries, definitions, axioms, and private names.
No depth, size, or pagination cutoff. A missing constant is a hard error.
The completion footer makes interrupted exports impossible to accept as complete.
-/
def run (moduleName : String) (dest : System.FilePath) (rootNames : Array String) : IO Unit := do
  if rootNames.isEmpty then
    throw <| IO.userError "Expected at least one root declaration"
  let env ← importModules #[{ module := moduleName.toName }] {}
  let mut queue : Array Name := #[]
  let mut seen : NameSet := {}
  for name in rootNames do
    let n := name.toName
    if (env.checked.get.find? n).isNone then
      throw <| IO.userError s!"Root not in checked Lean environment: {n}"
    if !seen.contains n then
      seen := seen.insert n
      queue := queue.push n
  let out ← IO.FS.Handle.mk dest IO.FS.Mode.write
  out.putStrLn (Json.mkObj [
      ("kind", toJson "manifest"),
      ("module", toJson moduleName),
      ("roots", toJson rootNames),
      ("source", toJson "Lean.Environment.checked; elaborated type and body"),
      ("complete", toJson false)]).compress
  let mut i := 0
  let mut edgeCount := 0
  while i < queue.size do
    let current := queue[i]!
    i := i + 1
    let some ci := env.checked.get.find? current
      | throw <| IO.userError s!"Referenced constant not found: {current}"
    let (ty, val) := refs ci
    edgeCount := edgeCount + ty.size + val.size
    let definingModule := match env.getModuleIdxFor? current with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => "<unknown>"
    out.putStrLn (nodeJson current definingModule ci).compress
    for n in ty do
      if !seen.contains n then
        seen := seen.insert n
        queue := queue.push n
    for n in val do
      if !seen.contains n then
        seen := seen.insert n
        queue := queue.push n
    if i % 10000 == 0 then
      IO.eprintln s!"Visited {i} declarations / queued {queue.size}"
  out.putStrLn (Json.mkObj [
      ("kind", toJson "complete"),
      ("nodes", toJson i),
      ("edges", toJson edgeCount),
      ("roots", toJson rootNames)]).compress
  out.flush
  IO.println s!"EXTRACTED {i} declarations and {edgeCount} elaborated references -> {dest}"
end ProofGraph

def main (args : List String) : IO Unit := do
  match args with
  | moduleName :: destination :: roots =>
    ProofGraph.run moduleName destination roots.toArray
  | _ => throw <| IO.userError
      "Usage: lean --run Extract.lean <module> <output.jsonl> <root> [root...]"
