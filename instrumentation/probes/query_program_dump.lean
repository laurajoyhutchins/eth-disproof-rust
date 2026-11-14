import Lean
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

/-!
Export the literal original QueryStreamProgram.program through Lean Meta.whnf.
The original term is in a noncomputable section, so ordinary lean --run
cannot compile direct references to it. Here the elaborator only normalizes
closed finite program expressions and checks every constructor before writing.
A stuck noncomputable term causes failure, never synthetic instruction output.
Run under the exact pinned OpenAI Lean and Mathlib checkouts.
-/

namespace NativeQueryTableExport
open Lean Meta Elab Command

private def numeric (e : Expr) : MetaM Nat := do
  let e ← whnf e
  match e with
  | .lit (.natVal v) => return v
  | _ => throwError m!"noncomputable term did not reduce to a numeral: {e}"

private def fin (e : Expr) : MetaM Nat :=
  numeric (mkProj ``Fin 0 e)

private def bit (e : Expr) : MetaM String := do
  let e ← whnf e
  match e with
  | .const name _ =>
    if name == ``Bool.true then return "1"
    if name == ``Bool.false then return "0"
    throwError m!"non-Boolean value: {e}"
  | _ => throwError m!"stuck non-Boolean value: {e}"

private def instr (e : Expr) : MetaM String := do
  let e ← whnf e
  match e.getAppFn with
  | .const name _ =>
    let a := e.getAppArgs
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.halt then return "halt"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.goto then
      return s!"goto:{← fin a[3]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.set then
      return s!"set:{← fin a[3]!}:{← bit a[4]!}:{← fin a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.copy then
      return s!"copy:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bnot then
      return s!"not:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.band then
      return s!"and:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bor then
      return s!"or:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.bxor then
      return s!"xor:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.branch then
      return s!"branch:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.push then
      return s!"push:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.peek then
      return s!"peek:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    if name == ``OAI.Algorithms.SubexponentialSAT.BitProgram.Instr.pop then
      return s!"pop:{← fin a[3]!}:{← fin a[4]!}:{← fin a[5]!}:{← fin a[6]!}"
    throwError m!"unknown finite instruction constructor: {name}"
  | _ => throwError m!"finite instruction failed to reduce: {e}"

elab "#export_query_program" : command => do
  let capValue ← liftIO <| IO.getEnv "M1_MAX_LABELS"
  let cap := ((capValue.getD "2000000").toNat?).getD 0
  if cap == 0 then throwError "M1_MAX_LABELS must be a positive decimal integer"
  let (r, s, l, entry, input, output, rows) ← liftTermElabM do
    let p := mkConst ``OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.program
    let typ ← inferType p
    let args := typ.getAppArgs
    if args.size != 3 then throwError "not a finite program"
    let r ← numeric args[0]!
    let s ← numeric args[1]!
    let l ← numeric args[2]!
    if r != 40 || s != 896 || l == 0 || l > cap then
      throwError m!"unsupported native query dimensions: {r} x {s} x {l}"
    let entry ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 2 p)
    let input ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 0 p)
    let output ← fin (mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 1 p)
    let mut rows : Array String := #[]
    let code := mkProj ``OAI.Algorithms.SubexponentialSAT.BitProgram.Program 3 p
    for i in [:l] do
      let limit := mkNatLit l
      let index := mkNatLit i
      let lt ← mkAppM ``LT.lt #[index, limit]
      let proof ← mkDecideProof lt
      let label := mkAppN (mkConst ``Fin.mk []) #[limit, index, proof]
      let result ← instr (mkApp code label)
      rows := rows.push s!"CODE|query|{i}|{result}"
    return (r, s, l, entry, input, output, rows)
  liftIO <| IO.println "PIN|query|4eaee87548250b2682affda7d05d947c05554bae|c2fb29983bb33229d5cf60729cd3d1e37b9b00ca"
  liftIO <| IO.println s!"PROGRAM|query|{r}|{s}|{l}|{entry}|{input}|{output}"
  for row in rows do
    liftIO <| IO.println row
  liftIO <| IO.println s!"END|query|{l}"

end NativeQueryTableExport

#export_query_program
