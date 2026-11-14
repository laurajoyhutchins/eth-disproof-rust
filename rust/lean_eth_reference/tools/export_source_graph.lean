import Lean
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.ProgramLinking

/-!
Emit a typed, source-elaborated StructuredCalls graph. Only a bounded Call
leaf is materialized: the parent command is NOT expanded into Fin-indexed code.
Refuse unknown constructors rather than translating an approximate operation.
The wrapper pins git source, Lean, and Mathlib before this command executes.
-/
namespace OriginalSourceGraph
open Lean Meta Elab Command

private def number (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => return n
  | _ => throwError m!"not a finite source numeric literal: {e}"

private def fin (e : Expr) : MetaM Nat :=
  number (mkProj ``Fin 0 e)

private def bit (e : Expr) : MetaM Nat := do
  let v ← whnf e
  match v with
  | .const n _ =>
    if n == ``Bool.true then return 1
    if n == ``Bool.false then return 0
    throwError m!"unrecognized source Boolean: {n}"
  | _ => throwError m!"source Boolean did not elaborate to a constructor: {v}"

private def operand (key : String) (n : Nat) : String := s!"{key}:{n}"

private def atom (e : Expr) : MetaM String := do
  let v ← whnf e
  match v.getAppFn with
  | .const n _ =>
    let a := v.getAppArgs
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.set then
      return s!"set:{← fin a[2]!}:{← bit a[3]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.copy then
      return s!"copy:{← fin a[2]!}:{← fin a[3]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.bnot then
      return s!"not:{← fin a[2]!}:{← fin a[3]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.band then
      return s!"and:{← fin a[2]!}:{← fin a[3]!}:{← fin a[4]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.bor then
      return s!"or:{← fin a[2]!}:{← fin a[3]!}:{← fin a[4]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.bxor then
      return s!"xor:{← fin a[2]!}:{← fin a[3]!}:{← fin a[4]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.push then
      return s!"push:{← fin a[2]!}:{← fin a[3]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.peek then
      return s!"peek:{← fin a[2]!}:{← fin a[3]!}:{← fin a[4]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Atom.pop then
      return s!"pop:{← fin a[2]!}:{← fin a[3]!}:{← fin a[4]!}"
    throwError m!"unsupported original atom constructor: {n}"
  | _ => throwError m!"original atom did not reduce to a constructor: {v}"

private def physicalInstr (e : Expr) : MetaM String := do
  let v ← whnf e
  match v.getAppFn with
  | .const n _ =>
    let a := v.getAppArgs
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.halt then
      return "halt"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.goto then
      return s!"goto:{← fin a[3]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.set then
      return s!"set:{← fin a[3]!}:{← bit a[4]!}:{← fin a[5]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.copy then
      return s!"copy:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bnot then
      return s!"not:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.band then
      return s!"and:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bor then
      return s!"or:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bxor then
      return s!"xor:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.branch then
      return s!"branch:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.push then
      return s!"push:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.peek then
      return s!"peek:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if n == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.pop then
      return s!"pop:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    throwError m!"unsupported original physical opcode: {n}"
  | _ => throwError m!"original physical instruction remains opaque: {v}"

private def boundedTable (p : Expr) (maxLabels : Nat) : MetaM Json := do
  let tp ← inferType p
  let args := tp.getAppArgs
  if args.size != 3 then throwError m!"call did not elaborate to a closed Program: {tp}"
  let r ← number args[0]!
  let s ← number args[1]!
  let l ← number args[2]!
  if r == 0 || s == 0 || l == 0 || r > 256 || s > 4096 || l > maxLabels then
    throwError m!"unsupported bounded callee dimensions: {r} {s} {l}"
  let entry ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 2 p)
  let input ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 0 p)
  let output ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 1 p)
  if entry >= l || input >= s || output >= s then
    throwError "callee has invalid finite entry or I/O port"
  let code := mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 3 p
  let mut rows : Array String := #[]
  for i in [:l] do
    let bound := mkNatLit l
    let index := mkNatLit i
    let proof ← mkDecideProof (← mkAppM ``LT.lt #[index, bound])
    let label := mkAppN (mkConst ``Fin.mk []) #[bound, index, proof]
    rows := rows.push (← physicalInstr (mkApp code label))
  return Json.mkObj [
    ("r", toJson r), ("s", toJson s), ("labels", toJson l),
    ("entry", toJson entry), ("input", toJson input),
    ("output", toJson output), ("code", toJson rows)
  ]

private def sourcePortMap (f : Expr) (domain ambient : Nat) : MetaM (Array Nat) := do
  let mut ports : Array Nat := #[]
  for i in [:domain] do
    let bound := mkNatLit domain
    let index := mkNatLit i
    let proof ← mkDecideProof (← mkAppM ``LT.lt #[index, bound])
    let port := mkAppN (mkConst ``Fin.mk []) #[bound, index, proof]
    let target ← fin (mkApp f port)
    if target >= ambient || ports.contains target then
      throwError m!"non-injective or out-of-range source port map at {i}: {target}"
    ports := ports.push target
  return ports

/-!
Preserve original ProgramLinking constructors as a typed graph instead of
reducing their entire `Fin labels → Instr` code to a table. Unknown cases
still use the existing bounded finite-leaf exporter.
-/
mutual
private partial def programGraph (p : Expr) (maxLabels fuel : Nat) : MetaM Json := do
  if fuel == 0 then throwError "source program linking exceeds recursion bound"
  let tp ← inferType p
  let args := tp.getAppArgs
  if args.size != 3 then
    throwError m!"source callee is not a closed BitProgram.Program: {tp}"
  let r ← number args[0]!
  let s ← number args[1]!
  let labels ← number args[2]!
  if r == 0 || s == 0 || labels == 0 || r > 256 ||
      s > 4096 || labels > maxLabels then
    throwError m!"source linked program dimensions unsupported: {r} {s} {labels}"
  match p.getAppFn with
  | .const n _ =>
    let a := p.getAppArgs
    if n == ``OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram &&
        a.size >= 3 then
      let source := a[a.size - 3]!
      let srcArgs := (← inferType source).getAppArgs
      if srcArgs.size != 3 then throwError "invalid source lift program type"
      let sr ← number srcArgs[0]!
      let ss ← number srcArgs[1]!
      return Json.mkObj [
        ("kind", toJson "lift"),
        ("r", toJson r), ("s", toJson s),
        ("registers", toJson (← sourcePortMap a[a.size - 2]! sr r)),
        ("stacks", toJson (← sourcePortMap a[a.size - 1]! ss s)),
        ("source", ← programGraph source maxLabels (fuel - 1))
      ]
    if n == ``OAI.Algorithms.SubexponentialSAT.ProgramLinking.linkInto &&
        a.size >= 6 then
      let left := a[a.size - 6]!
      let right := a[a.size - 5]!
      let leftArgs := (← inferType left).getAppArgs
      let rightArgs := (← inferType right).getAppArgs
      if leftArgs.size != 3 || rightArgs.size != 3 then
        throwError "invalid source linkInto child types"
      let lr ← number leftArgs[0]!
      let ls ← number leftArgs[1]!
      let rr ← number rightArgs[0]!
      let rs ← number rightArgs[1]!
      return Json.mkObj [
        ("kind", toJson "link_into"),
        ("r", toJson r), ("s", toJson s),
        ("left_registers", toJson (← sourcePortMap a[a.size - 4]! lr r)),
        ("left_stacks", toJson (← sourcePortMap a[a.size - 3]! ls s)),
        ("right_registers", toJson (← sourcePortMap a[a.size - 2]! rr r)),
        ("right_stacks", toJson (← sourcePortMap a[a.size - 1]! rs s)),
        ("left", ← programGraph left maxLabels (fuel - 1)),
        ("right", ← programGraph right maxLabels (fuel - 1))
      ]
    -- Large source-defined compiled callees are preserved as commands, never
    -- expanded into a Fin-indexed physical table. Small callees retain the
    -- separately verified table path for stable finite fixtures.
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled &&
        a.size == 5 && labels > 4096 then
      return Json.mkObj [
        ("kind", toJson "composed"),
        ("r", toJson r), ("s", toJson s),
        ("input", toJson (← fin a[3]!)),
        ("output", toJson (← fin a[4]!)),
        ("command", ← structured a[2]! maxLabels 512)
      ]
    if n == ``OAI.Algorithms.SubexponentialSAT.ProgramLinking.link &&
        a.size >= 2 then
      return Json.mkObj [
        ("kind", toJson "link"),
        ("left", ← programGraph a[a.size - 2]! maxLabels (fuel - 1)),
        ("right", ← programGraph a[a.size - 1]! maxLabels (fuel - 1))
      ]
    -- Preserve closed chains of named program aliases without forcing the
    -- physical instruction table. A chain may hide a link or a large compiled
    -- command; peel only zero-argument source definitions, still fuel-bounded.
    -- Ordinary concrete program bodies keep the bounded finite-table path.
    if a.isEmpty then
      match (← getConstInfo n) with
      | .defnInfo v =>
        match v.value.getAppFn with
        | .const head _ =>
          if head == ``OAI.Algorithms.SubexponentialSAT.ProgramLinking.liftProgram ||
             head == ``OAI.Algorithms.SubexponentialSAT.ProgramLinking.linkInto ||
             head == ``OAI.Algorithms.SubexponentialSAT.ProgramLinking.link ||
             (head == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled &&
              labels > 4096) ||
             (v.value.getAppArgs.isEmpty && head != n) then
            return (← programGraph v.value maxLabels (fuel - 1))
        | _ => pure ()
      | _ => pure ()
    boundedTable p (min maxLabels 4096)
  | _ => boundedTable p (min maxLabels 4096)

private partial def structured (e : Expr) (maxLabels fuel : Nat) : MetaM Json := do
  if fuel == 0 then throwError "source command nesting exceeded 512 nodes"
  -- Unwrap closed, named source definitions *one syntactic layer at a time*.
  -- Calling whnf on a named Nat.rec first would eagerly unfold its iterations,
  -- losing the exact constant-size Repeat representation. A name that resolves
  -- to an opaque axiom or an unsupported expression still fails closed.
  if e.getAppArgs.isEmpty then
    match e.getAppFn with
    | .const name _ =>
      match (← getConstInfo name) with
      | .defnInfo info =>
        return (← structured info.value maxLabels (fuel - 1))
      | _ => pure ()
    | _ => pure ()
  -- Inspect the *elaborated* recursor before whnf expands all repetitions.
  -- Accept only Nat.rec skip (fun _ previous => seq previous fixed) count,
  -- or its right-associated mirror. A different step or a state-dependent
  -- body is not a source repeat and must follow the ordinary refusal path.
  match e.getAppFn with
  | .const head _ =>
    if head == ``Nat.rec then
      let args := e.getAppArgs
      if args.size != 4 then
        throwError m!"unexpected Nat.rec command argument count {args.size}"
      let start ← structured args[1]! maxLabels (fuel - 1)
      if start.compress != (Json.mkObj [("kind", toJson "skip")]).compress then
        throwError "unsupported source Nat.rec: zero case is not a skip"
      let fixed ←
        match args[2]! with
        | .lam _ _ (.lam _ _ step _) _ =>
          match step.getAppFn with
          | .const op _ =>
            if op != ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq then
              throwError "unsupported source Nat.rec: step is not sequencing"
            let stepArgs := step.getAppArgs
            if stepArgs.size != 4 then
              throwError "unsupported source Nat.rec: unexpected sequencing arity"
            if stepArgs[2]! == Expr.bvar 0 then
              pure stepArgs[3]!
            else if stepArgs[3]! == Expr.bvar 0 then
              pure stepArgs[2]!
            else
              throwError "unsupported source Nat.rec: no direct accumulator"
          | _ => throwError "unsupported source Nat.rec: opaque step"
        | _ => throwError "unsupported source Nat.rec: not a two-argument step"
      let count ← number args[3]!
      if count > maxLabels then
        throwError "source repetition count exceeds bounded label budget"
      -- The fixed command is checked recursively, including its finite ABI.
      -- In particular, an index-dependent body cannot silently become fixed.
      let body ← structured fixed maxLabels (fuel - 1)
      return Json.mkObj [
        ("kind", toJson "repeat"), ("count", toJson count), ("body", body)
      ]
  | _ => pure ()
  let v ← whnf e
  match v.getAppFn with
  | .const n _ =>
    let a := v.getAppArgs
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.base then
      return (← basic a[2]! maxLabels (fuel - 1))
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.call then
      return Json.mkObj [("kind", toJson "call"),
        ("program", ← programGraph a[3]! maxLabels 64)]
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.seq then
      return Json.mkObj [("kind", toJson "seq"),
        ("first", ← structured a[2]! maxLabels (fuel - 1)),
        ("second", ← structured a[3]! maxLabels (fuel - 1))]
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.ite then
      return Json.mkObj [("kind", toJson "if"), ("test", toJson (← fin a[2]!)),
        ("yes", ← structured a[3]! maxLabels (fuel - 1)),
        ("no", ← structured a[4]! maxLabels (fuel - 1))]
    if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd.while then
      return Json.mkObj [("kind", toJson "while"), ("test", toJson (← fin a[2]!)),
        ("body", ← structured a[3]! maxLabels (fuel - 1))]
    throwError m!"unsupported StructuredCalls command: {n}"
  | _ => throwError m!"source StructuredCalls command is not a constructor: {v}"
where
  basic (e : Expr) (maxLabels fuel : Nat) : MetaM Json := do
    if fuel == 0 then throwError "source basic command depth exceeded"
    let v ← whnf e
    match v.getAppFn with
    | .const n _ =>
      let a := v.getAppArgs
      if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Cmd.skip then
        return Json.mkObj [("kind", toJson "skip")]
      if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Cmd.atom then
        return Json.mkObj [("kind", toJson "atom"), ("opcode", toJson (← atom a[2]!))]
      if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Cmd.seq then
        return Json.mkObj [("kind", toJson "seq"),
          ("first", ← basic a[2]! maxLabels (fuel - 1)),
          ("second", ← basic a[3]! maxLabels (fuel - 1))]
      if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Cmd.ite then
        return Json.mkObj [("kind", toJson "if"), ("test", toJson (← fin a[2]!)),
          ("yes", ← basic a[3]! maxLabels (fuel - 1)),
          ("no", ← basic a[4]! maxLabels (fuel - 1))]
      if n == ``OAI.Algorithms.SubexponentialSAT.StructuredProgram.Cmd.while then
        return Json.mkObj [("kind", toJson "while"), ("test", toJson (← fin a[2]!)),
          ("body", ← basic a[3]! maxLabels (fuel - 1))]
      throwError m!"unsupported StructuredProgram command: {n}"
    | _ => throwError m!"source StructuredProgram command is not a constructor: {v}"

end

syntax (name := exportOriginalSourceGraph)
  "#export_original_source_graph " ident str str : command

elab_rules : command
  | `(#export_original_source_graph $program:ident $id:str $blob:str) => do
    let programName := program.getId
    let label := id.getString
    let sourceBlob := blob.getString
    unless label.toList.all (fun c => c.isAlphanum || c == '_' || c == '-') do
      throwError "invalid source graph identifier"
    unless sourceBlob.length == 40 && sourceBlob.toList.all
      (fun c => c.isDigit || (c >= 'a' && c <= 'f')) do
      throwError "invalid source Git blob"
    -- Progress markers go only to stderr. The accepted stdout remains one
    -- canonical source JSON line, suitable for byte-bound certification.
    -- Enable on the expensive full-query export to locate a metaprogramming
    -- recursion failure without weakening any source or graph check.
    let diagnose := (← liftIO <| IO.getEnv "ORIGINAL_SOURCE_GRAPH_TRACE") == some "1"
    if diagnose then
      liftIO <| IO.eprintln "SOURCE_GRAPH_PHASE=source-identity-checked"
    let maxLabels := ((← liftIO <| IO.getEnv "ORIGINAL_MAX_LABELS").getD "4096").toNat?.getD 0
    if maxLabels == 0 || maxLabels > 1000000000 then
      throwError "ORIGINAL_MAX_LABELS must be 1..1000000000 (finite table leaves capped at 4096)"
    if diagnose then
      liftIO <| IO.eprintln "SOURCE_GRAPH_PHASE=resolve-original-definition"
    let body ← liftTermElabM do
      let info ← getConstInfo programName
      match info with
      | .defnInfo v => return v.value
      | _ => throwError m!"source program is not a definitional constant: {programName}"
    if diagnose then
      liftIO <| IO.eprintln "SOURCE_GRAPH_PHASE=infer-original-type"
    -- Split pure term elaboration from CommandElabM diagnostic IO.
    -- A type-level label normalization failure must have its own phase,
    -- rather than being mistaken for the complete command traversal.
    let (r, s, labelExpr) ← liftTermElabM do
      let tp ← inferType (mkConst programName)
      let a := tp.getAppArgs
      if a.size != 3 then throwError m!"expected a closed BitProgram.Program: {tp}"
      let r ← number a[0]!
      let s ← number a[1]!
      return (r, s, a[2]!)
    if diagnose then
      liftIO <| IO.eprintln s!"SOURCE_GRAPH_PHASE=normalize-type-level-label-count r={r} s={s}"
    let l ← liftTermElabM do number labelExpr
    if diagnose then
      liftIO <| IO.eprintln s!"SOURCE_GRAPH_PHASE=type-level-label-count-complete labels={l}"
    let graph ← liftTermElabM do
      if r == 0 || s == 0 || l == 0 || r > 256 || s > 4096 || l > maxLabels then
        throwError m!"source machine out of bounded test dimensions: {r} {s} {l}"
      -- A compiled command and a linked physical Program are both legitimate
      -- top-level entrypoints. Preserve their exact source label spaces; never
      -- wrap a linked root in an extra Cmd.call (which adds a halt site).
      let (kind, field, value) ←
        match body.getAppFn with
        | .const n _ =>
          if n == ``OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled then
            let args := body.getAppArgs
            if args.size != 5 then
              throwError m!"unexpected compiled command arity {args.size}"
            let command ← structured args[2]! maxLabels 512
            pure ("original-structured-source-v1", "command", command)
          else
            let program ← programGraph (mkConst programName) maxLabels 64
            pure ("original-linked-source-v1", "program", program)
        | _ =>
          let program ← programGraph (mkConst programName) maxLabels 64
          pure ("original-linked-source-v1", "program", program)
      let input ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 0
        (mkConst programName))
      let output ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 1
        (mkConst programName))
      return Json.mkObj [
        ("kind", toJson kind),
        ("source_commit", toJson "4eaee87548250b2682affda7d05d947c05554bae"),
        ("source_blob", toJson sourceBlob),
        ("declaration", toJson (toString programName)),
        ("id", toJson label),
        ("abi", Json.mkObj [("r", toJson r), ("s", toJson s),
          ("labels", toJson l), ("input", toJson input), ("output", toJson output)]),
        (field, value)
      ]
    if diagnose then
      liftIO <| IO.eprintln "SOURCE_GRAPH_PHASE=emit-complete-source-graph"
    liftIO <| IO.println graph.compress

end OriginalSourceGraph
