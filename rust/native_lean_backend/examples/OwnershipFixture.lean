import NativeRust
open Lean Elab Command

namespace OwnershipFixture
  def chain (x y : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x]
    let b := a.push y
    let c := b.push (x + y)
    c.getD 2 0
  def updateUnique (x y : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x, y]
    let b := a.set! 1 (y + 1)
    b.getD 1 0
  def preserveShared (x y : UInt64) : UInt64 :=
    let a : Array UInt64 := #[x, y]
    let b := a.set! 0 (x + 1)
    a.getD 0 0 + b.getD 0 0
end OwnershipFixture

-- Diagnostic of the exact optimized Lean 4.34.1 source IR used by the
-- canonical Reader. This is temporary and will be removed after diagnosis.
run_cmd do
  let targets := #[`OwnershipFixture.chain, `OwnershipFixture.updateUnique, `OwnershipFixture.preserveShared]
  let decls ← liftCoreM do
    Lean.Compiler.compile targets
    targets.mapM fun n => Lean.IR.findDecl n
  for i in [:decls.size] do
    if let some decl := decls[i]! then
      logInfo m!"SOURCE-OWNERSHIP-IR {targets[i]!}:\n{Lean.IR.declToString decl}"
    else
      logInfo m!"SOURCE-OWNERSHIP-IR missing {targets[i]!}"

#native_rust_package [OwnershipFixture.chain, OwnershipFixture.updateUnique, OwnershipFixture.preserveShared] to "examples/ownership-package"

run_cmd do
  let mut text := "use lean_generated::*;\n#[test] fn ownership_differential() {\n"
  let mut state : UInt64 := 0x31415926D00DCAFE
  for i in [:256] do
    state := state * 6364136223846793005 + 1442695040888963407
    let x : UInt64 := if i < 8 then UInt64.ofNat i else state
    let y : UInt64 := if i < 8 then UInt64.ofNat (7 - i) else state + 1
    text := text ++ s!"assert_eq!(chain({x.toNat}u64, {y.toNat}u64), {(OwnershipFixture.chain x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(updateUnique({x.toNat}u64, {y.toNat}u64), {(OwnershipFixture.updateUnique x y).toNat}u64);\n"
    text := text ++ s!"assert_eq!(preserveShared({x.toNat}u64, {y.toNat}u64), {(OwnershipFixture.preserveShared x y).toNat}u64);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/ownership-package/tests"
  liftIO <| IO.FS.writeFile "examples/ownership-package/tests/ownership.rs" text
  logInfo "Generated 768 Lean-evaluated ownership comparisons"
