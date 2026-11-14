import NativeRust

/-!
Actual Lean functions are compiled from their Lean 4.34.1 compiler IR.
The Rust tests below contain only inputs and independently Lean-evaluated
expectations, never replacement implementations of these algorithms.
-/
namespace ListFixture

@[noinline] def headOrZero (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: _ => x

@[noinline] def secondOrZero (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ :: rest =>
    match rest with
    | [] => 0
    | x :: _ => x

@[noinline] def prependSecond (head : Nat) (xs : List Nat) : Nat :=
  secondOrZero (head :: xs)

@[noinline] def isEmpty (xs : List Nat) : Bool :=
  match xs with
  | [] => true
  | _ :: _ => false

end ListFixture

#native_rust_package [ListFixture.headOrZero, ListFixture.secondOrZero,
  ListFixture.prependSecond, ListFixture.isEmpty] to "examples/list-package"

open Lean Elab Command

run_cmd do
  let mut tests := "use lean_generated::*;\n#[test] fn exact_original_lean_list_nat_oracles() {\n"
  let samples : Array (List Nat) :=
    #[[], [0], [1], [42, 3], [3, 42, 7], [0, 0, 0],
      [2^64, 2^128 + 7, 2^256 + 9],
      [2^512 + 3], [0, 2^1024 + 17],
      [2^256 + 91, 2^256 + 91]]
  for i in [:128] do
    let xs := if i < samples.size then samples[i]!
      else (List.range (i % 7)).map (fun j => (i + 1) * (j + 1))
    let sourceItems := xs.map (fun n => s!"__LeanValue::nat_from_decimal(\"{n}\")")
    let arg := "__LeanValue::list(vec![" ++ String.intercalate ", " sourceItems ++ "])"
    let first := ListFixture.headOrZero xs
    let second := ListFixture.secondOrZero xs
    let empty : Nat := if ListFixture.isEmpty xs then 1 else 0
    let appended := ListFixture.prependSecond (2^160 + i) xs
    tests := tests ++ s!"let input = {arg};\n"
    tests := tests ++ s!"assert_eq!(headOrZero(input.clone()).nat_to_decimal(), \"{first}\");\n"
    tests := tests ++ s!"assert_eq!(secondOrZero(input.clone()).nat_to_decimal(), \"{second}\");\n"
    tests := tests ++ s!"assert_eq!(isEmpty(input.clone()), {empty}u8);\n"
    tests := tests ++ s!"assert_eq!(prependSecond(__LeanValue::nat_from_decimal(\"{2^160 + i}\"), input.clone()).nat_to_decimal(), \"{appended}\");\n"
  tests := tests ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/list-package/tests"
  liftIO <| IO.FS.writeFile "examples/list-package/tests/list_nat_oracle.rs" tests
  logInfo "Generated 512 original-Lean List Nat oracle comparisons"
