import Lean

open Lean Elab Command

/-!
CI derives the machine-readable IR ledger from Lean's actual pinned inductive
constructor lists, not hand-entered tag numbers. A constructor addition or
reordering makes this command fail before generation. "conditional" is not
a claim of universal semantic support, only the restricted backend subset.
-/

private def expectedConstructors : Array (Name × Array Name) := #[
  (``Lean.IR.Decl, #[``Lean.IR.Decl.fdecl, ``Lean.IR.Decl.extern]),
  (``Lean.IR.IRType, #[``Lean.IR.IRType.float, ``Lean.IR.IRType.uint8, ``Lean.IR.IRType.uint16, ``Lean.IR.IRType.uint32, ``Lean.IR.IRType.uint64, ``Lean.IR.IRType.usize, ``Lean.IR.IRType.erased, ``Lean.IR.IRType.object, ``Lean.IR.IRType.tobject, ``Lean.IR.IRType.float32, ``Lean.IR.IRType.struct, ``Lean.IR.IRType.union, ``Lean.IR.IRType.tagged, ``Lean.IR.IRType.void]),
  (``Lean.IR.Arg, #[``Lean.IR.Arg.var, ``Lean.IR.Arg.erased]),
  (``Lean.IR.LitVal, #[``Lean.IR.LitVal.num, ``Lean.IR.LitVal.str]),
  (``Lean.IR.Expr, #[``Lean.IR.Expr.ctor, ``Lean.IR.Expr.reset, ``Lean.IR.Expr.reuse, ``Lean.IR.Expr.proj, ``Lean.IR.Expr.uproj, ``Lean.IR.Expr.sproj, ``Lean.IR.Expr.fap, ``Lean.IR.Expr.pap, ``Lean.IR.Expr.ap, ``Lean.IR.Expr.box, ``Lean.IR.Expr.unbox, ``Lean.IR.Expr.lit, ``Lean.IR.Expr.isShared]),
  (``Lean.IR.Alt, #[``Lean.IR.Alt.ctor, ``Lean.IR.Alt.default]),
  (``Lean.IR.FnBody, #[``Lean.IR.FnBody.vdecl, ``Lean.IR.FnBody.jdecl, ``Lean.IR.FnBody.set, ``Lean.IR.FnBody.setTag, ``Lean.IR.FnBody.uset, ``Lean.IR.FnBody.sset, ``Lean.IR.FnBody.inc, ``Lean.IR.FnBody.dec, ``Lean.IR.FnBody.del, ``Lean.IR.FnBody.case, ``Lean.IR.FnBody.ret, ``Lean.IR.FnBody.jmp, ``Lean.IR.FnBody.unreachable]),
]

private def conditionalConstructors : Array Name := #[
  ``Lean.IR.Decl.fdecl,
  ``Lean.IR.IRType.uint8,
  ``Lean.IR.IRType.uint16,
  ``Lean.IR.IRType.uint32,
  ``Lean.IR.IRType.uint64,
  ``Lean.IR.IRType.usize,
  ``Lean.IR.Arg.var,
  ``Lean.IR.LitVal.num,
  ``Lean.IR.Expr.fap,
  ``Lean.IR.Expr.lit,
  ``Lean.IR.Alt.ctor,
  ``Lean.IR.FnBody.vdecl,
  -- Restricted non-recursive, typed, scalar join continuations from #202.
  ``Lean.IR.FnBody.jdecl,
  ``Lean.IR.FnBody.jmp,
  ``Lean.IR.FnBody.case,
  ``Lean.IR.FnBody.ret,
  -- Bounded immutable object and source-defined all-boxed PAP/AP constructs.
  ``Lean.IR.IRType.object,
  ``Lean.IR.IRType.tobject,
  ``Lean.IR.IRType.tagged,
  ``Lean.IR.Expr.ctor,
  ``Lean.IR.Expr.proj,
  ``Lean.IR.Expr.pap,
  ``Lean.IR.Expr.ap,
  ``Lean.IR.Expr.box,
  ``Lean.IR.Expr.unbox,
  ``Lean.IR.FnBody.inc,
  ``Lean.IR.FnBody.dec,
  ``Lean.IR.FnBody.del,
]

run_cmd do
  let env ← getEnv
  let mut ledger := "family\tconstructor\tstatus\tsemantics\n"
  for (family, expected) in expectedConstructors do
    let some (.inductInfo info) := env.find? family
      | throwError "Missing pinned IR inductive {family}"
    unless info.ctors == expected.toList do
      throwError "Pinned IR ABI inventory mismatch for {family}: constructor order or membership changed"
    for constructor in info.ctors do
      let status := if conditionalConstructors.contains constructor then "conditional" else "refused"
      ledger := ledger ++ s!"{family}\t{constructor}\t{status}\tpinned-subset\n"
  let widths := #["UInt8", "UInt16", "UInt32", "UInt64", "USize"]
  let operations := #["add", "sub", "mul", "decEq", "decLt", "decLe"]
  for width in widths do
    for operation in operations do
      ledger := ledger ++ s!"primitive\t{width}.{operation}\tconditional\ttyped-binary-only\n"
  ledger := ledger ++ "primitive\t*\trefused\tunknown-or-external\n"
  liftIO <| IO.FS.writeFile "artifacts/ir-constructor-summary.tsv" ledger
