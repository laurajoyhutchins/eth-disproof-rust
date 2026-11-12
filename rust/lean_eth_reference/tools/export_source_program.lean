import Lean
import OAI.Algorithms.SubexponentialSAT.BitProgram

/-!
Source-driven finite-machine export. This command elaborates an ORIGINAL Lean
constant and only emits the exact source BitProgram.Instr constructors. It
never calls a host SAT implementation, guesses a return value, or rewrites an
unreduced source term. A failing, oversized or noncomputable reduction is a
hard refusal, not a partial success.
-/

namespace OriginalProgramExport
open Lean Meta Elab Command

private def numeric (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e with
  | .lit (.natVal n) => return n
  | _ => throwError m!"nonliteral source dimension or address: {e}"

private def finValue (e : Expr) : MetaM Nat :=
  numeric (mkProj ``Fin 0 e)

private def boolValue (e : Expr) : MetaM String := do
  let e ← whnf e
  match e with
  | .const name _ =>
    if name == ``Bool.true then return "1"
    if name == ``Bool.false then return "0"
    throwError m!"unsupported original Boolean constructor: {name}"
  | _ => throwError m!"nonliteral source Bool: {e}"

private def instruction (e : Expr) : MetaM String := do
  let e ← whnf e
  match e.getAppFn with
  | .const name _ =>
    let a := e.getAppArgs
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.halt then return "halt"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.goto then
      return s!"goto:{← finValue a[3]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.set then
      return s!"set:{← finValue a[3]!}:{← boolValue a[4]!}:{← finValue a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.copy then
      return s!"copy:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bnot then
      return s!"not:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.band then
      return s!"and:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}:{← finValue a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bor then
      return s!"or:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}:{← finValue a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bxor then
      return s!"xor:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}:{← finValue a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.branch then
      return s!"branch:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.push then
      return s!"push:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.peek then
      return s!"peek:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}:{← finValue a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.pop then
      return s!"pop:{← finValue a[3]!}:{← finValue a[4]!}:{← finValue a[5]!}:{← finValue a[6]!}"
    throwError m!"unknown source opcode: {name}"
  | _ => throwError m!"original instruction was not reduced to a constructor: {e}"

syntax (name := exportOriginalProgram)
  "#export_original_program " ident str str : command

elab_rules : command
  | `(#export_original_program $program:ident $id:str $blob:str) => do
    let programName := program.getId
    let label := id.getString
    let sourceBlob := blob.getString
    unless label.toList.all (fun c => c.isAlphanum || c == '_' || c == '-') do
      throwError "export program label contains unsafe characters"
    unless sourceBlob.length == 40 && sourceBlob.toList.all (fun c => c.isDigit || (c >= 'a' && c <= 'f')) do
      throwError "expected 40 lowercase hexadecimal source Git blob bytes"
    let maxLabels := ((← liftIO <| IO.getEnv "ORIGINAL_MAX_LABELS").getD "8192").toNat?.getD 0
    if maxLabels == 0 || maxLabels > 50000 then
      throwError "ORIGINAL_MAX_LABELS must be 1..50000"
    let (r, s, l, entry, input, output, rows) ← liftTermElabM do
      let p := mkConst programName
      let typ ← inferType p
      let args := typ.getAppArgs
      if args.size != 3 then throwError m!"original {programName} is not a closed Program r s l: {typ}"
      let r ← numeric args[0]!
      let s ← numeric args[1]!
      let l ← numeric args[2]!
      if r == 0 || s == 0 || r > 256 || s > 4096 || l == 0 || l > maxLabels then
        throwError m!"original program dimensions exceed bounded codegen: {r}×{s}×{l}"
      let entry ← finValue (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 2 p)
      let input ← finValue (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 0 p)
      let output ← finValue (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 1 p)
      if entry >= l || input >= s || output >= s then
        throwError "invalid original program entry or I/O ports"
      let code := mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 3 p
      let mut rows : Array String := #[]
      for i in [:l] do
        let bound := mkNatLit l
        let index := mkNatLit i
        let predicate ← mkAppM ``LT.lt #[index, bound]
        let proof ← mkDecideProof predicate
        let address := mkAppN (mkConst ``Fin.mk []) #[bound, index, proof]
        let actual ← instruction (mkApp code address)
        rows := rows.push s!"CODE|{label}|{i}|{actual}"
      return (r, s, l, entry, input, output, rows)
    -- Only print a table after all source instructions have reduced. The
    -- wrapper treats output as provisional until protocol/provenance validated.
    liftIO <| IO.println s!"PIN|{label}|4eaee87548250b2682affda7d05d947c05554bae|{sourceBlob}"
    liftIO <| IO.println s!"PROGRAM|{label}|{r}|{s}|{l}|{entry}|{input}|{output}"
    for row in rows do liftIO <| IO.println row
    liftIO <| IO.println s!"END|{label}|{l}"

end OriginalProgramExport
