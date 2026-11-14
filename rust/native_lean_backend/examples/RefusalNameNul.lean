import NativeRust

namespace NameBoundary

def bump (n : UInt64) : UInt64 := n + 1

end NameBoundary

open Lean Elab Command
run_cmd do
  let forbidden := "safe" ++ String.singleton (Char.ofNat 0) ++ "hidden"
  let _ ← liftCoreM <| NativeRust.compile `NameBoundary.bump forbidden
  throwError "embedded NUL was accepted as a Rust identifier"
