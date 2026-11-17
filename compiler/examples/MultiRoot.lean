import NativeRust
import Library

namespace PackageFixture
  def pipeline (x : UInt64) : UInt64 := Library.left x + Library.right x
  def combined (x : UInt64) : UInt64 := pipeline x + Library.bump x
  def select (x y : UInt64) : UInt64 := if x < y then combined x else pipeline y
end PackageFixture

#native_rust_package [PackageFixture.pipeline, PackageFixture.combined, PackageFixture.select]
  to "examples/native-package"

open Lean Elab Command
run_cmd do
  let mut text := "use lean_generated::*;\n#[test] fn lean_differential() {\n"
  let mut state : UInt64 := 0xC1517999A6210BDE
  for i in [:256] do
    state := state * 6364136223846793005 + 1442695040888963407
    let x := if i < 4 then UInt64.ofNat i else state
    let y := if i < 4 then UInt64.ofNat (4 - i) else state + 1
    text := text ++ s!"assert_eq!(pipeline({x.toNat}u64), {(PackageFixture.pipeline x).toNat}u64);\n"
    text := text ++ s!"assert_eq!(combined({x.toNat}u64), {(PackageFixture.combined x).toNat}u64);\n"
    text := text ++ s!"assert_eq!(select({x.toNat}u64, {y.toNat}u64), {(PackageFixture.select x y).toNat}u64);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/native-package/tests"
  liftIO <| IO.FS.writeFile "examples/native-package/tests/differential.rs" text
  logInfo "Generated 768 Lean-evaluated multi-root Cargo conformance assertions"
