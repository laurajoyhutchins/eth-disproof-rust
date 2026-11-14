import Lean

open Lean Elab Command

/-!
Constructor inventory is obtained from the active pinned Lean environment,
not from a hand-copied list of IR tags. CI compares it to the versioned
coverage classification. Newly introduced constructors cannot silently pass.
-/
run_cmd do
  let targets : Array Name := #[
    `Lean.IR.Decl, `Lean.IR.IRType, `Lean.IR.Arg, `Lean.IR.LitVal,
    `Lean.IR.Expr, `Lean.IR.Alt, `Lean.IR.FnBody
  ]
  let env ← getEnv
  let mut rows := "family\tconstructor\ttag\n"
  for target in targets do
    let some (.inductInfo info) := env.find? target
      | throwError "Pinned Lean compiler IR inductive missing: {target}"
    let constructors := info.ctors.toArray
    for i in [:constructors.size] do
      rows := rows ++ s!"{target}\t{constructors[i]!}\t{i}\n"
  liftIO <| IO.FS.createDirAll "artifacts"
  liftIO <| IO.FS.writeFile "artifacts/ir-constructors.tsv" rows
  logInfo "Emitted source-environment-derived IR constructor inventory"
