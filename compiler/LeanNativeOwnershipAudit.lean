import Lean
import Lean.Compiler.IR.Format

/-!
# Lean-native ownership / control-flow witness

This is a read-only consumer of *real* Lean 4.34.1 IR.Decl. It records
path-scoped instructions, source ownership flags and variable indices.
No replacement runtime, decoder, or source reconstruction is introduced.

A syntactic instruction inventory is NOT a physical RC trace, source-credit
proof, or generated-Rust correctness theorem. Branches and join definitions
are enumerated statically, not assumed to execute simultaneously.
-/

namespace LeanNativeOwnershipAudit

open Lean

structure Event where
  path : String
  op : String
  subject : String
  detail : String
  deriving Inhabited

private def event (path op subject detail : String) : Array Event :=
  #[⟨path, op, subject, detail⟩]

private def var (v : IR.VarId) : String :=
  "x_" ++ toString v.idx

private def join (j : IR.JoinPointId) : String :=
  "j_" ++ toString j.idx

private def exprEvent (path : String) (x : IR.VarId) : IR.Expr → Array Event
  | .ctor i ys => event path "Expr.ctor" (var x) s!"{i.name}/{i.cidx}/{ys.size}"
  | .reset n parent => event path "Expr.reset" (var x) s!"{var parent}/{n}"
  | .reuse parent i update ys =>
    event path "Expr.reuse" (var x) s!"{var parent}/{i.name}/{i.cidx}/{update}/{ys.size}"
  | .proj i parent => event path "Expr.proj" (var x) s!"{var parent}/{i}"
  | .uproj i parent => event path "Expr.uproj" (var x) s!"{var parent}/{i}"
  | .sproj i off parent => event path "Expr.sproj" (var x) s!"{var parent}/{i}/{off}"
  | .fap f ys => event path "Expr.fap" (var x) s!"{f}/{ys.size}"
  | .pap f ys => event path "Expr.pap" (var x) s!"{f}/{ys.size}"
  | .ap f ys => event path "Expr.ap" (var x) s!"{var f}/{ys.size}"
  | .box ty src => event path "Expr.box" (var x) s!"{repr ty}/{var src}"
  | .unbox src => event path "Expr.unbox" (var x) (var src)
  | .lit (.num n) => event path "Expr.lit.num" (var x) s!"{n}"
  | .lit (.str _) => event path "Expr.lit.str" (var x) "string"
  | .isShared src => event path "Expr.isShared" (var x) (var src)

/-- An ordered structural inventory, not an execution trace. The path
    distinguishes join-body vs join-continuation and alternative indices. -/
partial def events (path : String) : IR.FnBody → Array Event
  | .vdecl x _ e tail => exprEvent path x e ++ events path tail
  | .jdecl j ps value tail =>
    event path "FnBody.jdecl" (join j) s!"params={ps.size}" ++
      events (path ++ "/join_" ++ toString j.idx) value ++
      events (path ++ "/cont_" ++ toString j.idx) tail
  | .set x i _ tail =>
    event path "FnBody.set" (var x) s!"field={i}" ++ events path tail
  | .setTag x tag tail =>
    event path "FnBody.setTag" (var x) s!"tag={tag}" ++ events path tail
  | .uset x i _ tail =>
    event path "FnBody.uset" (var x) s!"field={i}" ++ events path tail
  | .sset x i off _ ty tail =>
    event path "FnBody.sset" (var x) s!"field={i}/{off}/{repr ty}" ++ events path tail
  | .inc x n check persistent tail =>
    event path "FnBody.inc" (var x) s!"n={n}/check={check}/persistent={persistent}" ++
      events path tail
  | .dec x n check persistent tail =>
    event path "FnBody.dec" (var x) s!"n={n}/check={check}/persistent={persistent}" ++
      events path tail
  | .del x tail =>
    event path "FnBody.del" (var x) "shell-only" ++ events path tail
  | .case tid x ty alts => Id.run do
    let mut result := event path "FnBody.case" (var x) s!"{tid}/{repr ty}/alts={alts.size}"
    for i in [:alts.size] do
      let alt := alts[i]!
      let category := match alt with
        | .ctor ci _ => s!"ctor:{ci.name}/{ci.cidx}"
        | .default _ => "default"
      let nested := path ++ "/alt_" ++ toString i
      result := result ++ event nested "Alt" (var x) category
      result := result ++ events nested alt.body
    return result
  | .ret (.var x) => event path "FnBody.ret" (var x) "var"
  | .ret .erased => event path "FnBody.ret" "erased" "erased"
  | .jmp j ys => event path "FnBody.jmp" (join j) s!"args={ys.size}"
  | .unreachable => event path "FnBody.unreachable" "_" "unreachable"

private def count (rows : Array Event) (op : String) : Nat :=
  (rows.filter (fun e => e.op == op)).size

/-- Source-compiler IR for unchanged roots, including negative candidates.
    Imported IR is never silently substituted with a synthetic body. -/
def inspect (roots : Array Name) : CoreM (String × String) := do
  if roots.isEmpty then throwError "Lean-native ownership audit: no original roots"
  -- Match the existing final-IR probe: ask Lean to compile these same roots.
  Compiler.compile roots
  let mut detail := "declaration\tpath\tordinal\top\tsubject\tdetail\n"
  let mut summary := "declaration\tinc\tdec\tdel\tjdecl\tproj\tisShared\tset\treset\treuse\n"
  for root in roots do
    let some decl ← IR.findDecl root
      | throwError "Lean-native ownership audit: no compiler IR for {root}"
    if let some blame := decl.getInfo.sorryDep? then
      throwError "Lean-native ownership audit: sorry dependency {blame} at {root}"
    let .fdecl _ _ _ body _ := decl
      | throwError "Lean-native ownership audit: no executable body for {root}"
    let rows := events "root" body
    for i in [:rows.size] do
      let r := rows[i]!
      detail := detail ++ s!"{root}\t{r.path}\t{i}\t{r.op}\t{r.subject}\t{r.detail}\n"
    summary := summary ++ s!"{root}\t{count rows "FnBody.inc"}\t{count rows "FnBody.dec"}\t{count rows "FnBody.del"}\t{count rows "FnBody.jdecl"}\t{count rows "Expr.proj"}\t{count rows "Expr.isShared"}\t{count rows "FnBody.set"}\t{count rows "Expr.reset"}\t{count rows "Expr.reuse"}\n"
  return (detail, summary)

def publish (path : System.FilePath) (manifest counts : String) : IO Unit := do
  if ← path.pathExists then
    throw <| IO.userError s!"Lean-native ownership audit: refusing existing output {path}"
  let temp ← IO.FS.createTempDir
  try
    IO.FS.writeFile (temp / "events.tsv") manifest
    IO.FS.writeFile (temp / "counts.tsv") counts
    IO.FS.rename temp path
  catch e =>
    try IO.FS.removeDirAll temp catch _ => pure ()
    throw e

end LeanNativeOwnershipAudit

open Lean Elab Command

syntax (name := leanNativeOwnershipCmd)
  "#lean_native_ownership_audit " "[" ident,* "]" " to " str : command

@[command_elab leanNativeOwnershipCmd]
def elabLeanNativeOwnershipCmd : CommandElab := fun stx => do
  match stx with
  | `(#lean_native_ownership_audit [$names:ident,*] to $dest:str) =>
    let roots := names.getElems.map (·.getId)
    let (manifest, counts) ← liftCoreM <| LeanNativeOwnershipAudit.inspect roots
    liftIO <| LeanNativeOwnershipAudit.publish dest.getString manifest counts
    logInfo m!"Audited genuine Lean IR ownership/control flow for {roots.size} roots"
  | _ => throwUnsupportedSyntax
