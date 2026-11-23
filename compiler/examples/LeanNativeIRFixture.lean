import LeanNativeRustIR
import LeanNativeIRSource

-- Two distinct original functions and their genuine compiler-IR closure.
#lean_native_ir_package [LeanNativeIRFixture.pipeline, LeanNativeIRFixture.add]
  to "artifacts/lean-native-ir-probe/arithmetic"

-- A separate admission gate: branch shapes can refuse without invalidating
-- independently verified straight-line/direct-call arithmetic.
#lean_native_ir_package [LeanNativeIRFixture.choose]
  to "artifacts/lean-native-ir-probe/branches"

open Lean Elab Command

/-- Independently executed Lean source is the oracle, not a reimplementation
    of the source functions inside the Rust code generator. -/
run_cmd do
  let path : System.FilePath := "artifacts/lean-native-ir-probe"
  let edges : Array UInt64 := #[
    0, 1, 2, 7, UInt64.ofNat (2^32-1),
    UInt64.ofNat (2^63), UInt64.ofNat (2^64-1)]
  let add := LeanNativeRustIR.symbol ``LeanNativeIRFixture.add
  let pipeline := LeanNativeRustIR.symbol ``LeanNativeIRFixture.pipeline
  let choose := LeanNativeRustIR.symbol ``LeanNativeIRFixture.choose
  let mut arithmetic := s!"use lean_native_ir_probe::{{{add}, {pipeline}}};\n#[test] fn lean_oracle_arithmetic() {{\n"
  let mut branches := s!"use lean_native_ir_probe::{choose};\n#[test] fn lean_oracle_branches() {{\n"
  for x in edges do
    for y in edges do
      let a := x.toNat
      let b := y.toNat
      arithmetic := arithmetic ++ s!"assert_eq!({add}({a}u64,{b}u64), {(LeanNativeIRFixture.add x y).toNat}u64);\n"
      arithmetic := arithmetic ++ s!"assert_eq!({pipeline}({a}u64,{b}u64), {(LeanNativeIRFixture.pipeline x y).toNat}u64);\n"
      branches := branches ++ s!"assert_eq!({choose}({a}u64,{b}u64), {(LeanNativeIRFixture.choose x y).toNat}u64);\n"
  arithmetic := arithmetic ++ "}\n"
  branches := branches ++ "}\n"
  liftIO <| IO.FS.createDirAll (path / "arithmetic" / "tests")
  liftIO <| IO.FS.createDirAll (path / "branches" / "tests")
  liftIO <| IO.FS.writeFile (path / "arithmetic" / "tests" / "oracle.rs") arithmetic
  liftIO <| IO.FS.writeFile (path / "branches" / "tests" / "oracle.rs") branches
  logInfo "49 input pairs × 3 original functions = 147 Lean-oracle checks"
