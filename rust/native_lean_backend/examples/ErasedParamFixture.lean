import NativeRust

namespace ErasedParamFixture

-- The proof is an actual source parameter, but Lean compiler IR marks it
-- IRType.erased. The generated Rust must never manufacture a proof object.
@[noinline] def acceptErased (n : Nat) (_h : n = n) : Nat :=
  n + 11

@[noinline] def through (n : Nat) : Nat :=
  acceptErased n rfl

end ErasedParamFixture

#native_rust_package [ErasedParamFixture.acceptErased, ErasedParamFixture.through]
  to "examples/erased-proof-package"

open Lean Elab Command
run_cmd do
  let root : Lean.Name := `ErasedParamFixture.acceptErased
  let some (.fdecl _ params _ _ _) ← liftCoreM <| Lean.IR.findDecl root
    | throwError "source proof-argument helper missing executable Lean compiler IR"
  unless params.any (fun p => p.ty == .erased) do
    throwError "source proof parameter was not IRType.erased in pinned Lean 4.34.1"
  liftIO <| IO.FS.writeFile
    "examples/erased-proof-package/original-ir.txt" (reprStr params)

  let mut test := "use lean_generated::*;\n#[test] fn source_proof_erasure_oracles() {\n"
  for i in [:64] do
    let n : Nat := if i % 11 == 0 then 2^256 + i else i*i + 7
    let expected := ErasedParamFixture.through n
    let direct := ErasedParamFixture.acceptErased n rfl
    test := test ++ s!"assert_eq!(through(__LeanValue::nat_from_decimal(\"{n}\")).nat_to_decimal(), \"{expected}\", \"through case {i}\");\n"
    test := test ++ s!"assert_eq!(acceptErased(__LeanValue::nat_from_decimal(\"{n}\"), ()).nat_to_decimal(), \"{direct}\", \"erased direct case {i}\");\n"
  test := test ++ "}\n"
  liftIO <| IO.FS.createDirAll "examples/erased-proof-package/tests"
  liftIO <| IO.FS.writeFile
    "examples/erased-proof-package/tests/erasure.rs" test
  logInfo "Generated 128 independent original-Lean proof-erasure comparisons"
