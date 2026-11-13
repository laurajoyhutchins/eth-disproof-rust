import NativeRust

namespace TaggedFixture
  inductive Light where
    | red
    | amber
    | green

  def rotate : Light → Light
    | .red => .amber
    | .amber => .green
    | .green => .red

  def score : Light → UInt64
    | .red => 5
    | .amber => 7
    | .green => 9

  def identity (x : Light) : Light := x

  def index : Light → Nat
    | .red => 0
    | .amber => 1
    | .green => 2
end TaggedFixture

#native_rust_closure TaggedFixture.rotate as "tag_rotate" to "examples/generated_tag_rotate.rs"
#native_rust_closure TaggedFixture.score as "tag_score" to "examples/generated_tag_score.rs"
#native_rust_closure TaggedFixture.identity as "tag_identity" to "examples/generated_tag_identity.rs"

open Lean Elab Command
run_cmd do
  let values : Array TaggedFixture.Light := #[.red, .amber, .green]
  let mut text := "{\n"
  for i in [:128] do
    let value := values[i % values.size]!
    let n := TaggedFixture.index value
    text := text ++ s!"assert_eq!(tag_rotate({n}usize),{TaggedFixture.index (TaggedFixture.rotate value)}usize);\n"
    text := text ++ s!"assert_eq!(tag_score({n}usize),{(TaggedFixture.score value).toNat}u64);\n"
    text := text ++ s!"assert_eq!(tag_identity({n}usize),{TaggedFixture.index (TaggedFixture.identity value)}usize);\n"
  text := text ++ "}\n"
  liftIO <| IO.FS.writeFile "examples/generated_tagged_differential.rs" text
  logInfo "Generated 384 independently evaluated nullary enum assertions"
