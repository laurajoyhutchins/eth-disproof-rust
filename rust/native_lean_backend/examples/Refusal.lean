import NativeRust
open Lean Elab Command

def nontrivialBranch (x : UInt64) : UInt64 := if x == 0 then 1 else x
def unsupportedString (x : String) : String := x ++ "!"
def unsupportedNat (x : Nat) : Nat := x / 2

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
    throwError "unsupported Nat semantics were silently accepted"
  let invalidName := NativeRust.emit decl "9not_valid"
  unless invalidName.startsWith "ERROR\n" do
    throwError "unsafe Rust name was accepted"
  let keywordName := NativeRust.emit decl "fn"
  unless keywordName.startsWith "ERROR\n" do
    throwError "Rust reserved keyword was accepted"
  logInfo "Unsupported Nat division and invalid Rust identifiers refused"
