import NativeRust

namespace BinaryFixture
  def answer : UInt64 := (41 : UInt64) + 1
  def small : UInt32 := (5 : UInt32) * 9 + 1
end BinaryFixture

#native_rust_binary BinaryFixture.answer to "examples/native-binary"
#native_rust_binary BinaryFixture.small to "examples/native-binary-small"

open Lean Elab Command
run_cmd do
  liftIO <| IO.FS.writeFile "artifacts/binary-expected.txt"
    s!"{BinaryFixture.answer.toNat}\n{BinaryFixture.small.toNat}\n"
