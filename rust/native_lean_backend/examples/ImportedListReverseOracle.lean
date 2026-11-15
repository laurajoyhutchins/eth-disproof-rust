import NativeRust

/-!
Original Lean 4.34.1 List.reverse is compiled directly from imported IR.
The code below generates test inputs and independently evaluates Lean outputs;
there is no replacement List.reverse implementation.
-/

open Lean Elab Command

run_cmd do
  let mut test := "#[test] fn imported_list_reverse_source_oracles() {\n"
  let samples : Array (List Nat) := #[
    [], [0], [1], [3, 5], [5, 3, 2], [0, 0, 0],
    [2^64], [2^128 + 7, 2^256 + 9],
    [2^512 + 3], [0, 2^1024 + 17],
    [2^256 + 91, 2^256 + 91]
  ]
  for i in [:128] do
    let xs := if i < samples.size then samples[i]!
      else (List.range (i % 13)).map (fun j => (i + 1) * (j * j + 1))
    let src := "__LeanValue::list(vec![" ++
      String.intercalate ", "
        (xs.map fun n => s!"__LeanValue::nat_from_decimal(\"{n}\")") ++ "])"
    let expected := List.reverse xs
    let values := "vec![" ++ String.intercalate ", "
      (expected.map fun n => s!"\"{n}\".to_owned()") ++ "]"
    test := test ++ s!"let result = public_root((), {src});\n"
    test := test ++ s!"assert_eq!(result.list_items().iter().map(|v| v.nat_to_decimal()).collect::<Vec<_>>(), {values}, \"source case {i}\");\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.createDirAll "artifacts/imported-probes/list-reverse-oracles"
  liftIO <| IO.FS.writeFile "artifacts/imported-probes/list-reverse-oracles/source_lean.rs" test
  logInfo "Generated 128 original Lean List.reverse oracle cases"
