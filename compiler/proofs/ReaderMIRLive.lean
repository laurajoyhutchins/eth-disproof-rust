import ReaderMIRSoundness

/-!
# Strict Lean-side interpretation of actual rustc 1.99.1 MIR text

This decoder reads the real MIR function emitted in the *same* rustc call
as the tested executable. Every basic block, operation, terminator and
successor must be understood. Unknown constructs fail closed.

Only opt-level=0 is presently admitted into the mathematical certificate:
the optimized MIR is still retained and tested, not yet formalized.
Rust's human-readable MIR printer and its relationship to machine
execution are separately trusted, unverified implementation boundaries.
-/

open Lean
open NativeRustScalarRefinement
open ReaderIRSoundness
open ReaderMIR

namespace ReaderMIRLive

private def trim (s : String) : String := s.trimAscii.toString

private def splitTwo (s separator : String) : Option (String × String) :=
  match s.splitOn separator with
  | [l, r] => some (l, r)
  | _ => none

private def register (s : String) : Option Nat := do
  let (pre, number) ← splitTwo s "_"
  if pre == "" then number.toNat? else none

private def blockId (s : String) : Option Nat := do
  let (pre, number) ← splitTwo s "bb"
  if pre == "" then number.toNat? else none

private def operand (s : String) : Option Nat :=
  match s.splitOn " " with
  | ["copy", name] => register name
  | ["move", name] => register name
  | _ => none

private def twoOperands (s : String) : Option (Nat × Nat) := do
  let (a, b) ← splitTwo s ", "
  return (← operand a, ← operand b)

private def callParts (s : String) : Option (String × String) := do
  let (name, afterOpen) ← splitTwo s "("
  let (args, afterClose) ← splitTwo afterOpen ")"
  if afterClose == "" then some (name, args) else none

private def pureInstruction (line : String) : Option Op := do
  let (left, right) ← splitTwo line " = "
  let dst ← register left
  let (rhs, suffix) ← splitTwo right ";"
  if suffix != "" then none else
    if rhs.startsWith "const " then do
      let (pre, numberText) ← splitTwo rhs "const "
      let (number, ending) ← splitTwo numberText "_u64"
      if pre != "" || ending != "" then none else
        let n ← number.toNat?
        if n < modulus then some (.literal dst n) else none
    else if rhs.startsWith "copy " || rhs.startsWith "move " then do
      let src ← operand rhs
      some (.copy dst src)
    else do
      let (fnName, args) ← callParts rhs
      let (a, b) ← twoOperands args
      if fnName == "Eq" then some (.eq dst a b)
      else if fnName == "Lt" then some (.lt dst a b)
      else if fnName == "Le" then some (.le dst a b)
      else none

private def mirCall (dst : Nat) (body : String) : Option Op := do
  let (fnName, args) ← callParts body
  if fnName == "core::num::<impl u64>::wrapping_add" then do
    let (a, b) ← twoOperands args
    some (.add dst a b)
  else if fnName == "core::num::<impl u64>::wrapping_mul" then do
    let (a, b) ← twoOperands args
    some (.mul dst a b)
  else if fnName == "<u8 as From<bool>>::from" then do
    let src ← operand args
    some (.boolToTag dst src)
  else none

private def panicMessage : String :=
  "Arguments::<'_>::from_str_nonconst(const \"internal error: entered unreachable code: invalid Lean Bool tag\")"

private def terminalInstruction (line : String) :
    Option (List Op × Exit) := do
  if line == "return;" then
    some ([], .ret)
  else if line.startsWith "goto -> " then do
    let (pre, rest) ← splitTwo line "goto -> "
    let (target, suffix) ← splitTwo rest ";"
    if pre != "" || suffix != "" then none else
      let id ← blockId target
      some ([], .goto id)
  else if line.startsWith "switchInt(" then do
    let (pre, rest) ← splitTwo line "switchInt("
    if pre != "" then none else
      let (tagText, tail) ← splitTwo rest ") -> ["
      let tag ← operand tagText
      let (branches, suffix) ← splitTwo tail "];"
      if suffix != "" then none else
        match branches.splitOn ", " with
        | [falseText, trueText, otherText] => do
            let (fPrefix, fLabel) ← splitTwo falseText "0: "
            let (tPrefix, tLabel) ← splitTwo trueText "1: "
            let (oPrefix, oLabel) ← splitTwo otherText "otherwise: "
            if fPrefix != "" || tPrefix != "" || oPrefix != "" then none else
              let falsePc ← blockId fLabel
              let truePc ← blockId tLabel
              let otherwisePc ← blockId oLabel
              some ([], .switch tag falsePc truePc otherwisePc)
        | _ => none
  else do
    let (left, right) ← splitTwo line " = "
    let dest ← register left
    if right.endsWith " -> unwind continue;" then do
      let (expr, suffix) ← splitTwo right " -> unwind continue;"
      if suffix != "" then none else
        let (fnName, args) ← callParts expr
        if fnName != "std::rt::panic_fmt" then none else
          let _ ← operand args
          some ([], .panic)
    else do
      let (expr, nextText) ← splitTwo right " -> [return: "
      let (nextBlock, suffix) ← splitTwo nextText ", unwind continue];"
      if suffix != "" then none else
        let next ← blockId nextBlock
        if expr == panicMessage then
          some ([], .goto next)
        else do
          let op ← mirCall dest expr
          some ([op], .goto next)

private def statementBlock : List String → List Op → Option Block
  | [], _ => none
  | line :: rest, revOps =>
      let line := trim line
      if line.isEmpty then
        statementBlock rest revOps
      else if rest.all (fun s => (trim s).isEmpty) then do
        let (finalOps, terminator) ← terminalInstruction line
        some ⟨revOps.reverse ++ finalOps, terminator⟩
      else do
        let op ← pureInstruction line
        statementBlock rest (op :: revOps)

private def bodyLines : List String → List String →
    Option (List String × List String)
  | [], _ => none
  | line :: rest, acc =>
      if trim line == "}" then
        some (acc.reverse, rest)
      else
        bodyLines rest (line :: acc)

/-- Total, instruction-count-bounded decoder: the fuel decreases even
when the parser skips an entire block with its enclosed lines. -/
private def parseBlocks : Nat → List String → Graph → Option Graph
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | fuel + 1, line :: rest, acc =>
      let line := trim line
      if line.isEmpty then
        parseBlocks fuel rest acc
      else if line == "}" then
        if rest.all (fun x => (trim x).isEmpty) then
          some acc.reverse
        else none
      else do
        let (idText, opening) ← splitTwo line ": "
        if opening != "{" then none else
          let id ← blockId idText
          if acc.any (fun entry => entry.1 == id) then none else
            let (body, remaining) ← bodyLines rest []
            let block ← statementBlock body []
            parseBlocks fuel remaining ((id, block) :: acc)

/-- Only field/scope metadata is ignored. Every executable line must be
parsed into one of the typed operations or terminators above. -/
private def startBlocks (budget : Nat) : List String → Option Graph
  | [] => none
  | line :: rest =>
      let line := trim line
      if line.startsWith "bb" then
        parseBlocks budget (line :: rest) []
      else if line.isEmpty || line == "}" ||
          line.startsWith "scope " ||
          line.startsWith "let " ||
          line.startsWith "debug " then
        startBlocks budget rest
      else none

/-- No parser fallback or permissive else branch: a single changed MIR
opcode, selector, successor, literal, or extra executable line is refused. -/
def decodeFunction (text : String) : Option Graph :=
  match text.splitOn "\n" with
  | first :: rest =>
      if first != "fn certified_scalar(_1: u64, _2: u64) -> u64 {" then none
      else do
        let graph ← startBlocks rest.length rest
        if (lookup graph 0).isSome then some graph else none
  | _ => none

structure Certificate where
  source : ReaderRustStatement.Certificate
  mirText : String
  graph : Graph
  decoded : decodeFunction mirText = some graph
  fuel : Nat
  graphAgreement :
    symRun fuel graph 0 sourceSymbols =
      some source.live.linked.source.program

/-- This is the only way the actual-MIR certificate is produced: read
the real rustc .function.mir file, decode all executable blocks in Lean,
reify their symbolic result, and compare it to the *independently*
certified Reader/original-Lean-IR program. -/
def certify (root : Name) (text : String) : CoreM Certificate := do
  let source ← ReaderRustStatement.certify root
  match hd : decodeFunction text with
  | none =>
      throwError "real rustc MIR contains unknown syntax or CFG: {root}"
  | some graph =>
      let fuel := 1000
      if h : symRun fuel graph 0 sourceSymbols =
          some source.live.linked.source.program then
        return {source, mirText := text, graph, decoded := hd,
                fuel, graphAgreement := h}
      else
        throwError "real MIR CFG has different all-input semantics from original Lean IR: {root}"

/-- Formal all-input execution of the admitted MIR graph equals actual
source UInt64 arithmetic and case semantics. This is a theorem about
the independently defined small MIR interpreter and the *decoded graph*.
It does not assert that rustc machine code is a proven implementation. -/
theorem actual_mir_cfg_refines (c : Certificate) (a b : UInt64) :
    decodeFunction c.mirText = some c.graph ∧
    ∃ sourceValue,
      ReaderIRBoolSoundness.BodyRuns c.source.live.linked.source.body
        (ReaderIRSoundness.initialRuntime c.source.live.linked.source.left
          c.source.live.linked.source.right a b)
        ReaderIRBoolSoundness.initialSourceTests sourceValue ∧
      realRun c.fuel c.graph 0 (initialRegisters a b) =
        some sourceValue.toNat := by
  let value := evalActualProgram (ReaderIRSoundness.inputWords a b)
    c.source.live.linked.source.program
  refine ⟨c.decoded, value, ?_, ?_⟩
  · exact ReaderIRBoolSoundness.body_sound
      c.source.live.linked.source.sourceProof
      (ReaderIRSoundness.inputWords a b)
      (ReaderIRSoundness.initialRuntime c.source.live.linked.source.left
        c.source.live.linked.source.right a b)
      ReaderIRBoolSoundness.initialSourceTests
      (ReaderIRBoolSoundness.initial_agrees
        c.source.live.linked.source.left
        c.source.live.linked.source.right a b)
  · exact certified_mir_refines c.graph c.fuel
      c.source.live.linked.source.program c.graphAgreement a b

end ReaderMIRLive

#print axioms ReaderMIRLive.actual_mir_cfg_refines

open Lean Elab Command

run_cmd do
  for root in #[`ScalarFixture.plus, `ScalarFixture.straightChain,
                `ScalarFixture.choose, `ScalarFixture.nested] do
    let fixture := root.toString.replace "ScalarFixture." ""
    let path := s!"artifacts/reader-rust-exec-{fixture}-opt0.function.mir"
    let text ← liftIO <| IO.FS.readFile path
    let c ← liftCoreM <| ReaderMIRLive.certify root text
    let _ := ReaderMIRLive.actual_mir_cfg_refines c
    liftIO <| IO.FS.writeFile s!"artifacts/reader-mir-cfg-{fixture}.txt"
      ("source_program=\n" ++
        (repr c.source.live.linked.source.program).pretty 100 ++
        "\ninterpreted_mir_graph=\n" ++ (repr c.graph).pretty 100 ++ "\n")
    logInfo m!"Actual rustc MIR CFG admitted to all-input source theorem: {root}, blocks={c.graph.length}"
  -- The decoder, not just the earlier shell footprint check, must refuse a
  -- real arithmetic-operator substitution and reversed branch successors.
  let path := "artifacts/reader-rust-exec-choose-opt0.function.mir"
  let original ← liftIO <| IO.FS.readFile path
  let badOp := original.replace "wrapping_add(" "wrapping_sub("
  if badOp == original || (ReaderMIRLive.decodeFunction badOp).isSome then
    throwError "MIR decoder admitted unsupported wrapping subtraction"
  let badEdges := original.replace
    "switchInt(copy _3) -> [0: bb4, 1: bb3, otherwise: bb2];"
    "switchInt(copy _3) -> [0: bb3, 1: bb4, otherwise: bb2];"
  if badEdges == original then
    throwError "original MIR Bool-switch negative control has drifted"
  let source ← liftCoreM <| ReaderRustStatement.certify `ScalarFixture.choose
  if let some badGraph := ReaderMIRLive.decodeFunction badEdges then
    if ReaderMIR.symRun 1000 badGraph 0 ReaderMIR.sourceSymbols ==
        some source.live.linked.source.program then
      throwError "MIR semantic checker admitted reversed Bool successors"
  let badTrap := original.replace
    "switchInt(copy _3) -> [0: bb4, 1: bb3, otherwise: bb2];"
    "switchInt(copy _3) -> [0: bb4, 1: bb3, otherwise: bb4];"
  if badTrap == original then
    throwError "MIR trap-path negative control did not modify original source"
  if let some badGraph := ReaderMIRLive.decodeFunction badTrap then
    if (ReaderMIR.symRun 1000 badGraph 0 ReaderMIR.sourceSymbols).isSome then
      throwError "MIR semantic checker admitted invalid-tag return path"
  let badDuplicate := original.replace "bb8: {" "bb1: {"
  if badDuplicate == original ||
      (ReaderMIRLive.decodeFunction badDuplicate).isSome then
    throwError "MIR parser admitted duplicate basic-block identifier"
  logInfo "Actual MIR checker refused substituted arithmetic, reversed Bool edges, nontrapping invalid tag, and duplicate block"
