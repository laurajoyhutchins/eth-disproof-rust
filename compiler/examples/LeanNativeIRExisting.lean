import NativeRust
import LeanNativeIRSource

-- The unchanged original declarations are consumed by the canonical Rust FFI
-- backend. This package is independent of the Lean-native experiment package.
#native_rust_package [LeanNativeIRFixture.pipeline,
                      LeanNativeIRFixture.add,
                      LeanNativeIRFixture.choose]
  to "artifacts/lean-native-ir-probe/existing"

open Lean Elab Command

run_cmd do
  let dir : System.FilePath := "artifacts/lean-native-ir-probe/existing/tests"
  let edges : Array UInt64 := #[
    0, 1, 2, 7, UInt64.ofNat (2^32-1),
    UInt64.ofNat (2^63), UInt64.ofNat (2^64-1)]
  let mut code := "use lean_generated::{add, pipeline, choose};\n#[test] fn original_source_oracle() {\n"
  for x in edges do
    for y in edges do
      let a := x.toNat
      let b := y.toNat
      code := code ++ s!"assert_eq!(add({a}u64,{b}u64), {(LeanNativeIRFixture.add x y).toNat}u64);\n"
      code := code ++ s!"assert_eq!(pipeline({a}u64,{b}u64), {(LeanNativeIRFixture.pipeline x y).toNat}u64);\n"
      code := code ++ s!"assert_eq!(choose({a}u64,{b}u64), {(LeanNativeIRFixture.choose x y).toNat}u64);\n"
  liftIO <| IO.FS.createDirAll dir
  liftIO <| IO.FS.writeFile (dir / "oracle.rs") (code ++ "}\n")
  logInfo "147 original Lean-to-existing-Rust checks generated"
