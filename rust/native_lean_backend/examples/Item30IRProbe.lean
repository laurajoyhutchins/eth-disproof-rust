import Lean

namespace Item30Probe

def natAdd (x y : Nat) : Nat := x + y
def natSub (x y : Nat) : Nat := x - y
def natMul (x y : Nat) : Nat := x * y
def intAdd (x y : Int) : Int := x + y
def strAppend (x y : String) : String := x ++ y
def strBytes (x : String) : Nat := x.utf8ByteSize
def strChars (x : String) : Nat := x.length
def arrayPush (x : Array UInt64) (y : UInt64) : Array UInt64 := x.push y
def arraySize (x : Array UInt64) : Nat := x.size
def listReverse (x : List UInt64) : List UInt64 := x.reverse

end Item30Probe

open Lean Elab Command

run_cmd do
  let targets : Array Name := #[
    `Item30Probe.natAdd, `Item30Probe.natSub, `Item30Probe.natMul,
    `Item30Probe.intAdd,
    `Item30Probe.strAppend, `Item30Probe.strBytes, `Item30Probe.strChars,
    `Item30Probe.arrayPush, `Item30Probe.arraySize, `Item30Probe.listReverse
  ]
  let mut report := "# Lean 4.34.1 generated executable IR for item 30 probes\n"
  for name in targets do
    Lean.Compiler.compile #[name]
    let some decl ← Lean.IR.findDecl name
      | throwError "Missing pinned executable IR for {name}"
    report := report ++ s!"\n## {name}\n{toString decl}\n"
  liftIO <| IO.FS.createDirAll "artifacts"
  liftIO <| IO.FS.writeFile "artifacts/item30-ir-probes.txt" report
  logInfo m!"Probed {targets.size} original Lean definitions into compiler IR"
