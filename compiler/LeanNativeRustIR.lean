import Lean

/-!
Experimental, deliberately narrow Lean-native Rust emitter.
Consumes the real Lean 4.34.1 `Lean.IR.Decl` and never constructs a substitute IR.
The existing Rust backend, runtime, and source definitions are unchanged.

Admitted: UInt64 parameters/results, UInt64 arithmetic, scalar UInt8 Bool
conditions, exact Bool two-way cases, direct closed calls, and returns.
No heap values, ownership events, joins, effects, or implicit primitive fallback.
-/

namespace LeanNativeRustIR

open Lean

private def refusal {α : Type} (kind detail : String) : Except String α :=
  .error ((Json.mkObj [
    ("status", .str "refused"),
    ("construct", .str kind),
    ("reason", .str detail)
  ]).compress)

private def scalarType : IR.IRType → Except String String
  | .uint64 => .ok "u64"
  | .uint8 => .ok "u8"
  | other => refusal "IRType" s!"unsupported scalar type {repr other}"

/-- Injective UTF-8 byte encoding, including punctuation and non-ASCII names. -/
def symbol (name : Name) : String :=
  "lean_" ++ name.toString.toUTF8.foldl
    (fun s b => s ++ toString b.toNat ++ "_") ""

private def localName (v : IR.VarId) : String :=
  "_v" ++ toString v.idx

private def knownPrimitive (n : Name) : Bool :=
  #[``UInt64.add, ``UInt64.sub, ``UInt64.mul,
    ``UInt64.decEq, ``UInt64.decLt, ``UInt64.decLe].contains n

private def renderArg : IR.Arg → Except String String
  | .var id => .ok (localName id)
  | .erased => refusal "Arg.erased" "erased argument in scalar call/return"

private def renderArgs (args : Array IR.Arg) : Except String (Array String) :=
  args.mapM renderArg

private def renderExpr (known : Array Name) (result : IR.IRType)
    (e : IR.Expr) : Except String String := do
  match e with
  | .lit (.num n) =>
    if result == .uint64 && n < 2^64 then
      return s!"{n}u64"
    if result == .uint8 && n < 256 then
      return s!"{n}u8"
    return ← refusal "Expr.lit" s!"literal outside supported width/type: {n}"
  | .fap f args =>
    let xs ← renderArgs args
    if knownPrimitive f then
      unless xs.size == 2 do
        return ← refusal "Expr.fap" s!"primitive {f}: expected two arguments"
      let a := xs[0]!
      let b := xs[1]!
      if f == ``UInt64.add && result == .uint64 then
        return s!"{a}.wrapping_add({b})"
      if f == ``UInt64.sub && result == .uint64 then
        return s!"{a}.wrapping_sub({b})"
      if f == ``UInt64.mul && result == .uint64 then
        return s!"{a}.wrapping_mul({b})"
      if f == ``UInt64.decEq && result == .uint8 then
        return s!"u8::from({a} == {b})"
      if f == ``UInt64.decLt && result == .uint8 then
        return s!"u8::from({a} < {b})"
      if f == ``UInt64.decLe && result == .uint8 then
        return s!"u8::from({a} <= {b})"
      return ← refusal "Expr.fap" s!"type mismatch in {f}"
    unless known.contains f do
      return ← refusal "Expr.fap" s!"unresolved or unsupported direct call {f}"
    unless result == .uint64 do
      return ← refusal "Expr.fap" "non-UInt64 user call result"
    return symbol f ++ "(" ++ String.intercalate ", " xs.toList ++ ")"
  | _ => refusal "Expr" "unsupported expression constructor"

private partial def callsInBody : IR.FnBody → Array Name
  | .vdecl _ _ (.fap f _) tail => #[f] ++ callsInBody tail
  | .vdecl _ _ _ tail => callsInBody tail
  | .case _ _ _ alts =>
    alts.foldl (fun s a => s ++ callsInBody a.body) #[]
  | .jdecl _ _ value tail => callsInBody value ++ callsInBody tail
  | .set _ _ _ tail => callsInBody tail
  | .setTag _ _ tail => callsInBody tail
  | .uset _ _ _ tail => callsInBody tail
  | .sset _ _ _ _ _ tail => callsInBody tail
  | .inc _ _ _ _ tail => callsInBody tail
  | .dec _ _ _ _ tail => callsInBody tail
  | .del _ tail => callsInBody tail
  | _ => #[]

private def blockName (j : IR.JoinPointId) : String :=
  "_block" ++ toString j.idx

/-- Join closures have scalar captured environments. A jump is admitted only
    to a previously declared lexical join; self/mutual recursion refuse. -/
private partial def renderBody (known : Array Name)
    (joins : Array (IR.JoinPointId × Nat)) : IR.FnBody → Except String String
  | .vdecl x ty e rest => do
    let t ← scalarType ty
    let rhs ← renderExpr known ty e
    let tail ← renderBody known joins rest
    return s!"let {localName x}: {t} = {rhs};\n{tail}"
  | .ret arg => do
    let a ← renderArg arg
    return s!"{a}\n"
  | .jdecl j ps value tail => do
    if joins.any (fun p => p.1 == j) then
      return ← refusal "FnBody.jdecl" "duplicate join id"
    let mut params := #[]
    for p in ps do
      if p.borrow then
        return ← refusal "FnBody.jdecl" "borrowed join parameter"
      let t ← scalarType p.ty
      params := params.push s!"{localName p.x}: {t}"
    let body ← renderBody known joins value
    let cont ← renderBody known (joins.push (j, ps.size)) tail
    return "let " ++ blockName j ++ " = |" ++
      String.intercalate ", " params.toList ++
      "| -> u64 {\n" ++ body ++ "};\n" ++ cont
  | .jmp j args => do
    let some (_, arity) := joins.find? (fun entry => entry.1 == j)
      | return ← refusal "FnBody.jmp" "out-of-scope or recursive join"
    unless args.size == arity do
      return ← refusal "FnBody.jmp" "join parameter arity mismatch"
    let xs ← renderArgs args
    return blockName j ++ "(" ++ String.intercalate ", " xs.toList ++ ")\n"
  | .case tyName x ty alts => do
    unless tyName == ``UInt8 && ty == .uint8 && alts.size == 2 do
      return ← refusal "FnBody.case" s!"requires Bool 2 alternatives: type={tyName}, irType={repr ty}, n={alts.size}"
    let (.ctor f falseBody) := alts[0]!
      | return ← refusal "FnBody.case" "first branch is not constructor, possibly default"
    let (.ctor t trueBody) := alts[1]!
      | return ← refusal "FnBody.case" "second branch is not constructor, possibly default"
    unless f.name == ``Bool.false && f.cidx == 0 &&
           t.name == ``Bool.true && t.cidx == 1 do
      return ← refusal "FnBody.case" s!"constructor mismatch: {f.name}[{f.cidx}], {t.name}[{t.cidx}]"
    let no ← renderBody known joins falseBody
    let yes ← renderBody known joins trueBody
    return "match " ++ localName x ++ " {\n0 => {\n" ++ no ++ "},\n1 => {\n" ++ yes ++ "},\n_ => unreachable!(\"invalid Lean Bool tag\"),\n}\n"
  | .unreachable => refusal "FnBody.unreachable" "unreachable is not admitted"
  | _ => refusal "FnBody" "unsupported instruction constructor"

/-- All executable dependencies remain Lean IR objects until emission. -/
private def closure (roots : Array Name) : CoreM (Array IR.Decl) := do
  if roots.isEmpty then throwError "Lean-native emitter: empty root set"
  let mut missing := #[]
  for root in roots do
    if (← IR.findDecl root).isNone then
      missing := missing.push root
  unless missing.isEmpty do
    Compiler.compile missing
  let mut queue := roots
  let mut seen : Std.HashSet Name := {}
  let mut decls := #[]
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    if seen.contains n then continue
    seen := seen.insert n
    if seen.size > 64 then
      throwError "Lean-native emitter refused: closure limit 64"
    let some decl ← IR.findDecl n
      | throwError "Lean-native emitter refused: no compiler IR for {n}"
    if let some blame := decl.getInfo.sorryDep? then
      throwError "Lean-native emitter refused: sorry dependency {blame}"
    decls := decls.push decl
    if let .fdecl _ _ _ body _ := decl then
      for call in callsInBody body do
        unless knownPrimitive call do
          queue := queue.push call
  return decls

private def renderDecl (known : Array Name) : IR.Decl → Except String String
  | .extern n _ _ _ => refusal "Decl.extern" s!"external declaration {n}"
  | .fdecl n params result body _ => do
    unless result == .uint64 do
      return ← refusal "Decl.fdecl" s!"non-UInt64 function return {n}"
    let mut ps := #[]
    for p in params do
      unless p.ty == .uint64 && !p.borrow do
        return ← refusal "Param" s!"unsupported parameter type/borrow in {n}"
      ps := ps.push s!"{localName p.x}: u64"
    let code ← renderBody known #[] body
    return "pub fn " ++ symbol n ++ "(" ++
      String.intercalate ", " ps.toList ++ ") -> u64 {\n" ++
      code ++ "}\n"

/-- Pure code generation on genuine compiler IR. Any failure discards all output. -/
def generate (decls : Array IR.Decl) : Except String String := do
  let names := decls.map (·.name)
  let mut out := "#![forbid(unsafe_code)]\n\n"
  for d in decls do
    out := out ++ (← renderDecl names d) ++ "\n"
  return out

def publish (dest : System.FilePath) (source : String) : IO Unit := do
  if ← dest.pathExists then
    throw <| IO.userError s!"Lean-native emitter refused existing destination {dest}"
  let tmp ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (tmp / "src")
    IO.FS.writeFile (tmp / "src" / "lib.rs") source
    IO.FS.writeFile (tmp / "Cargo.toml")
      "[package]\nname = \"lean_native_ir_probe\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\npath = \"src/lib.rs\"\n\n[workspace]\n"
    IO.FS.rename tmp dest
  catch err =>
    try IO.FS.removeDirAll tmp catch _ => pure ()
    throw err

def compilePackage (roots : Array Name) : CoreM String := do
  let decls ← closure roots
  match generate decls with
  | .error why => throwError "Lean-native emitter refused: {why}"
  | .ok code => return code

end LeanNativeRustIR

open Lean Elab Command

syntax (name := leanNativeRustIRCmd)
  "#lean_native_ir_package " "[" ident,* "]" " to " str : command

@[command_elab leanNativeRustIRCmd]
def elabLeanNativeRustIRCmd : CommandElab := fun stx => do
  match stx with
  | `(#lean_native_ir_package [$roots:ident,*] to $dest:str) =>
    let names := roots.getElems.map (·.getId)
    let source ← liftCoreM <| LeanNativeRustIR.compilePackage names
    liftIO <| LeanNativeRustIR.publish dest.getString source
    logInfo m!"Lean-native IR experiment emitted {names.size} source roots"
  | _ => throwUnsupportedSyntax
