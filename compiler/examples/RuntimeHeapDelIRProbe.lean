import Lean
import Lean.Compiler.IR.Format
import RuntimeHeapDelKernels

/-!
Inspect final Lean.IR.Decl, not source syntax or an intermediate LCNF pass.
An absent del must stay an explicit negative result. This probe does not
execute Reader-generated Rust and cannot certify source_del equivalence.
-/
namespace RuntimeHeapDel.IRProbe

open Lean Elab Command

private partial def countDel : Lean.IR.FnBody → Nat
  | .vdecl _ _ _ tail => countDel tail
  | .jdecl _ _ value tail => countDel value + countDel tail
  | .set _ _ _ tail => countDel tail
  | .setTag _ _ tail => countDel tail
  | .uset _ _ _ tail => countDel tail
  | .sset _ _ _ _ _ tail => countDel tail
  | .inc _ _ _ _ tail => countDel tail
  | .dec _ _ _ _ tail => countDel tail
  | .del _ tail => 1 + countDel tail
  | .case _ _ _ alts =>
      alts.foldl (fun n alt => n + countDel alt.body) 0
  | .ret .. | .jmp .. | .unreachable => 0

private partial def countJoins : Lean.IR.FnBody → Nat
  | .vdecl _ _ _ tail => countJoins tail
  | .jdecl _ _ value tail => 1 + countJoins value + countJoins tail
  | .set _ _ _ tail => countJoins tail
  | .setTag _ _ tail => countJoins tail
  | .uset _ _ _ tail => countJoins tail
  | .sset _ _ _ _ _ tail => countJoins tail
  | .inc _ _ _ _ tail => countJoins tail
  | .dec _ _ _ _ tail => countJoins tail
  | .del _ tail => countJoins tail
  | .case _ _ _ alts =>
      alts.foldl (fun n alt => n + countJoins alt.body) 0
  | .ret .. | .jmp .. | .unreachable => 0

run_cmd do
  let roots : Array Lean.Name := #[
    `RuntimeHeapDel.rebuild,
    `RuntimeHeapDel.rebuildOrDiscard,
    `RuntimeHeapDel.rebuildOrExtract,
    `RuntimeHeapDel.rebuildThenExtract,
    `RuntimeHeapDel.rebuildOrDiscardByPayload,
    `RuntimeHeapDel.rebuildOrExtractByPayload
  ]
  -- Uses the same real compiler entrypoint as NativeRust.resolveCompilerIR?.
  liftCoreM <| Lean.Compiler.compile roots
  let mut rows := "declaration\tfinal_ir_del\tfinal_ir_jdecl\n"
  let mut totalDel := 0
  let mut completeIR := ""
  for root in roots do
    let some decl ← liftCoreM <| Lean.IR.findDecl root
      | throwError "No final Lean.IR declaration for {root}"
    let .fdecl _ _ _ body _ := decl
      | throwError "Final compiler declaration is not a function: {root}"
    let deletions := countDel body
    let joins := countJoins body
    totalDel := totalDel + deletions
    -- Preserve the real final IR, including control flow and ownership ops.
    completeIR := completeIR ++ s!"=== {root} ===\n" ++
      Lean.IR.declToString decl ++ "\n"
    rows := rows ++ s!"{root}\t{deletions}\t{joins}\n"
    logInfo m!"Pinned final IR {root}: del={deletions}, joins={joins}"
    -- The two source-derived positive witnesses are now independently
    -- observed on the pinned final IR. Fail closed if compiler drift
    -- drops the real del or changes the join structure.
    if root == `RuntimeHeapDel.rebuildOrDiscardByPayload ||
       root == `RuntimeHeapDel.rebuildOrExtractByPayload then
      unless deletions == 1 && joins == 2 do
        throwError "Source-derived final IR witness drift: {root}: del={deletions}, joins={joins}"
  liftIO <| IO.FS.createDirAll "artifacts"
  liftIO <| IO.FS.writeFile "artifacts/source-del-final-ir.tsv" rows
  liftIO <| IO.FS.writeFile "artifacts/source-del-final-ir.txt" completeIR
  let status := if totalDel == 0 then "NO_SOURCE_DEL_CANDIDATE" else "SOURCE_DEL_FOUND_NOT_EXECUTED"
  unless totalDel >= 2 do
    throwError "Pinned final IR lost the source-derived deletion witnesses"
  liftIO <| IO.FS.writeFile "artifacts/source-del-final-ir-status.txt"
    s!"status={status}\nsource=RuntimeHeapDelKernels.lean\ncompiler=Lean.Compiler.compile\nfinal_ir=Lean.IR.findDecl\nfinal_del_count={totalDel}\nemitted_ir_source_del=NOT_YET_ESTABLISHED\n"
  logInfo m!"Source del candidate result: {status}"

end RuntimeHeapDel.IRProbe
