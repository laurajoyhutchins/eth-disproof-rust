import NativeRust
open Lean Elab Command

def nontrivialBranch (x : UInt64) : UInt64 := if x == 0 then 1 else x
def unsupportedString (x : String) : String := x ++ "!"
def unsupportedNat (x y : Nat) : Nat := Nat.land x y

run_cmd do
  liftCoreM <| Lean.Compiler.compile #[`unsupportedString]
  let some decl ← liftCoreM <| Lean.IR.findDecl `unsupportedString
    | throwError "no IR to test refusal"
  let report := NativeRust.emit decl "nontrivial_branch"
  unless report.startsWith "ERROR\n" do
    throwError "unsupported String was silently accepted"
  logInfo "Unsupported String refused by native Rust backend"
  liftCoreM <| Lean.Compiler.compile #[`unsupportedNat]
  let some natDecl ← liftCoreM <| Lean.IR.findDecl `unsupportedNat
    | throwError "no Nat IR to test refusal"
  let natReport := NativeRust.emit natDecl "unsupported_nat"
  unless natReport.startsWith "ERROR\n" do
    throwError "unsupported Nat bitwise primitive was silently accepted"
  unless (natReport.splitOn "\"construct\":\"Primitive\"").length == 2 do
    throwError "unsupported Nat operation lost its source primitive refusal category"
  let invalidName := NativeRust.emit decl "9not_valid"
  unless invalidName.startsWith "ERROR\n" do
    throwError "unsafe Rust name was accepted"
  unless (invalidName.splitOn "\"construct\":\"Decl\"").length == 2 do
    throwError "invalid Rust public symbol lost its declaration refusal category"
  let keywordName := NativeRust.emit decl "fn"
  unless keywordName.startsWith "ERROR\n" do
    throwError "Rust reserved keyword was accepted"
  unless (keywordName.splitOn "\"construct\":\"Decl\"").length == 2 do
    throwError "reserved Rust symbol lost its declaration refusal category"
  logInfo "Unsupported Nat bitwise operation and invalid Rust identifiers refused"
