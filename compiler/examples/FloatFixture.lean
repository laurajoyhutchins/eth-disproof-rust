import NativeRust

namespace FloatFixture
  def add (a b : Float) : Float := a + b
  def sub (a b : Float) : Float := a - b
  def mul (a b : Float) : Float := a * b
end FloatFixture

#native_rust_closure FloatFixture.add as "float_add" to "examples/generated_float_add.rs"
#native_rust_closure FloatFixture.sub as "float_sub" to "examples/generated_float_sub.rs"
#native_rust_closure FloatFixture.mul as "float_mul" to "examples/generated_float_mul.rs"

open Lean Elab Command
run_cmd do
  let values : Array Float := #[0.0, 1.0, 2.0, 0.5, 1.5, -1.0, -2.0, -0.5]
  let mut lines := "{\n"
  for i in [:128] do
    let a := values[i % values.size]!
    let b := values[(i * 3 + 1) % values.size]!
    lines := lines ++ s!"assert_eq!(float_add({a}f64,{b}f64),{(FloatFixture.add a b)}f64);\n"
    lines := lines ++ s!"assert_eq!(float_sub({a}f64,{b}f64),{(FloatFixture.sub a b)}f64);\n"
    lines := lines ++ s!"assert_eq!(float_mul({a}f64,{b}f64),{(FloatFixture.mul a b)}f64);\n"
  lines := lines ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_float_differential.rs" lines
  logInfo "Generated 384 original-Lean finite Float comparisons"
