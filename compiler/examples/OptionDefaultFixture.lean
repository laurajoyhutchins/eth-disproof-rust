import NativeRust
open Lean Elab Command

namespace OptionDefaultFixture

@[noinline] def onSome (value : Option Nat) : Nat :=
  match value with
  | some x => x
  | _ => 0

@[noinline] def onNone (value : Option Nat) : Nat :=
  match value with
  | none => 7
  | _ => 11

def roundTrip (n : Nat) (present : Bool) : Nat :=
  onSome (if present then some n else none)

def branch (n : Nat) (present : Bool) : Nat :=
  onNone (if present then some n else none)

end OptionDefaultFixture

#native_rust_package [OptionDefaultFixture.roundTrip, OptionDefaultFixture.branch] to "examples/option-default-package"

run_cmd do
  let mut source := ""
  for root in #[`OptionDefaultFixture.onSome, `OptionDefaultFixture.onNone] do
    let decl ← liftCoreM do
      if (← Lean.IR.findDecl root).isNone then
        Lean.Compiler.compile #[root]
      let some d ← Lean.IR.findDecl root
        | throwError "original Option source IR missing for {root}"
      return d
    source := source ++ s!"ORIGINAL {root}\n{decl}\nEND {root}\n"
  liftIO <| IO.FS.writeFile "examples/option-default-package/original-ir.txt" source

run_cmd do
  let mut test := "use lean_generated::{roundTrip, branch};\n#[test] fn source_option_default_oracles() {\n"
  for i in [:256] do
    let n := if i % 7 == 0 then 2^1024 + i else if i % 5 == 0 then 2^256 + 3*i else i*19
    let present := i % 3 != 0
    let b : Nat := if present then 1 else 0
    let a := OptionDefaultFixture.roundTrip n present
    let c := OptionDefaultFixture.branch n present
    test := test ++ s!"let n = lean_generated::__LeanValue::nat_from_decimal(\"{n}\");\n"
    test := test ++ s!"assert_eq!(roundTrip(n.clone(), {b}u8).nat_to_decimal(), \"{a}\");\n"
    test := test ++ s!"assert_eq!(branch(n, {b}u8).nat_to_decimal(), \"{c}\");\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/option-default-package/tests"
  liftIO <| IO.FS.writeFile "examples/option-default-package/tests/oracle.rs" test
  logInfo "Generated 512 original-Lean Option constructor/default oracles"
