import NativeRust
import Item30IRProbe

#native_rust Item30Probe.natAdd as "sem_nat_add" to "examples/generated_sem_nat_add.rs"
#native_rust Item30Probe.natSub as "sem_nat_sub" to "examples/generated_sem_nat_sub.rs"
#native_rust Item30Probe.natMul as "sem_nat_mul" to "examples/generated_sem_nat_mul.rs"
#native_rust Item30Probe.intAdd as "sem_int_add" to "examples/generated_sem_int_add.rs"
#native_rust Item30Probe.strAppend as "sem_str_append" to "examples/generated_sem_str_append.rs"
#native_rust Item30Probe.strBytes as "sem_str_bytes" to "examples/generated_sem_str_bytes.rs"
#native_rust Item30Probe.strChars as "sem_str_chars" to "examples/generated_sem_str_chars.rs"
#native_rust Item30Probe.arrayPush as "sem_array_push" to "examples/generated_sem_array_push.rs"
#native_rust Item30Probe.arraySize as "sem_array_size" to "examples/generated_sem_array_size.rs"
#native_rust Item30Probe.listReverse as "sem_list_reverse" to "examples/generated_sem_list_reverse.rs"

open Lean Elab Command

private def valueArrayExpr (module : String) (values : Array UInt64) : String :=
  let entries := values.toList.map (fun v => s!"{module}::Value::UInt64({v.toNat}u64)")
  s!"{module}::Value::array(vec![{String.intercalate ", " entries}])"

private def valueListExpr (module : String) (values : List UInt64) : String :=
  let entries := values.map (fun v => s!"{module}::Value::UInt64({v.toNat}u64)")
  s!"{module}::Value::list(vec![{String.intercalate ", " entries}])"

/-- Encode data as decimal UTF-8 bytes rather than interpolating Rust string literals. -/
private def rustStringExpr (module : String) (value : String) : String :=
  let bytes := value.toUTF8.data.toList.map (fun b => s!"{b.toNat}u8")
  s!"{module}::Value::string(std::str::from_utf8(&[{String.intercalate ", " bytes}]).unwrap())"

run_cmd do
  let mut out := "fn main() {\n"
  let nats : Array Nat := #[
    0, 1, 2, 7, 42, 2^32-1, 2^64-1, 2^64, 2^127,
    2^128-1, 2^128, 2^255, 2^256+17, 2^512+123
  ]
  for i in [:nats.size] do
    let a := nats[i]!
    let b := nats[(i*7+3) % nats.size]!
    out := out ++ s!"    assert_eq!(nat_add::sem_nat_add(nat_add::Value::nat(\"{a}\"), nat_add::Value::nat(\"{b}\")), nat_add::Value::nat(\"{Item30Probe.natAdd a b}\"));\n"
    out := out ++ s!"    assert_eq!(nat_sub::sem_nat_sub(nat_sub::Value::nat(\"{a}\"), nat_sub::Value::nat(\"{b}\")), nat_sub::Value::nat(\"{Item30Probe.natSub a b}\"));\n"
    out := out ++ s!"    assert_eq!(nat_mul::sem_nat_mul(nat_mul::Value::nat(\"{a}\"), nat_mul::Value::nat(\"{b}\")), nat_mul::Value::nat(\"{Item30Probe.natMul a b}\"));\n"
  let ints : Array Int := #[
    0, -1, 1, -7, 42, Int.ofNat (2^64),
    -(Int.ofNat (2^127)), Int.ofNat (2^128+3),
    -(Int.ofNat (2^255)), Int.ofNat (2^512+17)
  ]
  for i in [:ints.size] do
    let a := ints[i]!
    let b := ints[(i*3+5) % ints.size]!
    out := out ++ s!"    assert_eq!(int_add::sem_int_add(int_add::Value::int(\"{a}\"), int_add::Value::int(\"{b}\")), int_add::Value::int(\"{Item30Probe.intAdd a b}\"));\n"
  let strings : Array String := #["", "é", "🧮", "𐐷", "한글", "naïve", "नमस्ते", "n̄",
    "quote\"slash\\", "line\nbreak", String.singleton (Char.ofNat 0)]
  for i in [:strings.size] do
    let a := strings[i]!
    let b := strings[(i+3) % strings.size]!
    let lhs := rustStringExpr "str_append" a
    let rhs := rustStringExpr "str_append" b
    let expected := rustStringExpr "str_append" (Item30Probe.strAppend a b)
    let byteArg := rustStringExpr "str_bytes" a
    let charsArg := rustStringExpr "str_chars" a
    out := out ++ s!"    assert_eq!(str_append::sem_str_append({lhs}, {rhs}), {expected});\n"
    out := out ++ s!"    assert_eq!(str_bytes::sem_str_bytes({byteArg}), str_bytes::Value::nat(\"{Item30Probe.strBytes a}\"));\n"
    out := out ++ s!"    assert_eq!(str_chars::sem_str_chars({charsArg}), str_chars::Value::nat(\"{Item30Probe.strChars a}\"));\n"
  let arrays : Array (Array UInt64) := #[
    #[], #[0], #[1, 2, 3], #[UInt64.ofNat (2^64-1), 7],
    #[0, 1, 2, 3, 4, 5, 6, 7]
  ]
  for i in [:arrays.size] do
    let a := arrays[i]!
    let element := UInt64.ofNat (i*17+3)
    let aInput := valueArrayExpr "array_push" a
    let aExpected := valueArrayExpr "array_push" (Item30Probe.arrayPush a element)
    let bInput := valueArrayExpr "array_size" a
    let elementInput := s!"{element.toNat}u64"
    out := out ++ s!"    assert_eq!(array_push::sem_array_push({aInput}, {elementInput}), {aExpected});\n"
    out := out ++ s!"    assert_eq!(array_size::sem_array_size({bInput}), array_size::Value::nat(\"{Item30Probe.arraySize a}\"));\n"
    let list := a.toList
    out := out ++ s!"    assert_eq!(list_reverse::sem_list_reverse({valueListExpr "list_reverse" list}), {valueListExpr "list_reverse" (Item30Probe.listReverse list)});\n"
  out := out ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_semantic_cases.rs" out
  logInfo "Generated 100 original-Lean arbitrary precision, Unicode, collection and edge cases"
