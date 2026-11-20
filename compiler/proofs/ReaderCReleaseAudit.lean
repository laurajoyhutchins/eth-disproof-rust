import Lean
import ReaderCReleaseSemantics

/-!
# Replay actual Lean 4.34.1 C final-release and heap-stamp checkpoints.

Source is an independent C executable using real Lean C refcounts,
not an artificial trace constructed from this model. The importer
validates exact order, allocation identity, and branch footprints.
A zero RC after a last-reference free is an observer's *tombstone*,
not a forbidden physical read of freed memory.

This is bounded observational testing of a separate mathematical
semantics. It does not prove the C++ program correct for all inputs.
-/
namespace ReaderCReleaseAudit
open ReaderCReleaseSemantics

structure Row where
  caseName : String
  event : String
  outcome : String
  physical : Physical
  parentId : Nat
  childId : Nat
  oldId : Nat
  freshId : Nat
  deriving Repr

def number (field : String) : Except String Nat :=
  match field.toNat? with
  | some x => pure x
  | none => throw s!"invalid numeric field '{field}'"

def bit (field : String) : Except String Bool := do
  let n ← number field
  if n == 0 then pure false
  else if n == 1 then pure true
  else throw s!"invalid Boolean field '{field}'"

def slot : String → Except String StampSlot
  | "old" => pure .old
  | "spent" => pure .spent
  | "fresh" => pure .fresh
  | name => throw s!"unknown stamp slot '{name}'"

def parse (line : String) : Except String Row := do
  match line.splitOn "\t" with
  | [name, event, outcome, parent, child, old, fresh, field, pending,
      borrowed, stamp, parentId, childId, oldId, freshId] =>
      let parentRC ← number parent
      let childRC ← number child
      let oldRC ← number old
      let freshRC ← number fresh
      let childField ← bit field
      let freshPending ← bit pending
      let childBorrowed ← bit borrowed
      let stampSlot ← slot stamp
      return {
        caseName := name
        event
        outcome
        physical := {
          parentRC, childRC, oldRC, freshRC,
          childField, stampSlot, freshPending, childBorrowed
        }
        parentId := (← number parentId)
        childId := (← number childId)
        oldId := (← number oldId)
        freshId := (← number freshId)
      }
  | _ => throw s!"incorrect C final-release TSV arity: '{line}'"

def instruction : String → Except String Op
  | "borrowChild" => pure .borrowChild
  | "decOld" => pure .decOld
  | "incFresh" => pure .incFresh
  | "storeFresh" => pure .storeFresh
  | "incChild" => pure .incChild
  | "decParent" => pure .decParent
  | "decLastChild" => pure .decLastChild
  | "shellDel" => pure .shellDel
  | name => throw s!"unknown C release op '{name}'"

def expected : List (String × List String) := [
  ("heapFreshFinal", [
    "borrowChild", "decOld", "incFresh", "storeFresh", "decParent"
  ]),
  ("heapFreshRetained", [
    "borrowChild", "decOld", "incFresh", "storeFresh",
    "incChild", "decParent", "decLastChild"
  ]),
  ("oldStampFinal", ["decParent"])
]

def sameIdentity (initial next : Row) : Bool :=
  next.caseName == initial.caseName &&
  next.parentId == initial.parentId &&
  next.childId == initial.childId &&
  next.oldId == initial.oldId &&
  next.freshId == initial.freshId

/-- A measured selected-C-model transition has a corresponding source
credit step. This lemma is conditional on the model transition: it does
not assert that arbitrary C++ executions implement `cStep`. -/
theorem modeled_c_step_has_source (s : Source) (op : Op) (measured : Physical)
    (h : cStep (represent s) op = some measured) :
    ∃ next, sourceStep s op = some next ∧ represent next = measured := by
  rw [cStep_represent] at h
  cases hs : sourceStep s op with
  | none =>
      simp [hs] at h
  | some next =>
      refine ⟨next, rfl, ?_⟩
      simpa [hs] using h

/-- Independently replay both the source-credit ledger and the selected
physical C model against each actual observed C checkpoint. The induction
state is the source ledger, not the previous physical count row. -/
def verifySteps (first : Row) :
    List String → Source → List Row →
      Except String (List Row × Nat)
  | [], _, rest => pure (rest, 0)
  | opName :: restOps, source, r :: remaining => do
      if !sameIdentity first r || r.event != opName || r.outcome != "ok" then
        throw s!"C release event order or pointer identity mismatch in {first.caseName}: {opName}"
      let op ← instruction opName
      let some next := sourceStep source op
        | throw s!"Source-credit model refused observed C release in {first.caseName}/{opName}"
      unless represent next == r.physical do
        throw s!"C release source-credit mismatch in {first.caseName}/{opName}: expected {repr (represent next)}, measured {repr r.physical}"
      let predicted := cStep (represent source) op
      unless predicted == some r.physical do
        throw s!"C release physical-branch mismatch in {first.caseName}/{opName}: predicted {repr predicted}, measured {repr r.physical}"
      let (tail, n) ← verifySteps first restOps next remaining
      pure (tail, n + 1)
  | _ :: _, _, [] =>
      throw s!"missing C release event for {first.caseName}"

def verifyOne (name : String) (events : List String) (rows : List Row) :
    Except String (List Row × Nat) := do
  match rows with
  | [] => throw s!"missing C release initial state for {name}"
  | first :: rest =>
      if first.caseName != name || first.event != "initial" ||
         first.outcome != "ok" then
        throw s!"expected initial C release state for {name}"
      if first.parentId == 0 || first.childId == 0 ||
         first.oldId == 0 || first.freshId == 0 ||
         first.parentId == first.childId ||
         first.parentId == first.oldId ||
         first.parentId == first.freshId ||
         first.childId == first.oldId ||
         first.childId == first.freshId ||
         first.oldId == first.freshId then
        throw s!"invalid or aliased C release pointer identity for {name}"
      if first.physical.oldRC < 2 || first.physical.freshRC == 0 then
        throw s!"missing protected external heap stamp roots for {name}"
      let startingSource := initial (first.physical.oldRC - 1) first.physical.freshRC
      unless first.physical == represent startingSource do
        throw s!"C release initial state violates source-owned field credits: {name}"
      let (tail, n) ← verifySteps first events startingSource rest
      pure (tail, n + 1)

def verify (rows : List Row) : Except String Nat := do
  let mut remaining := rows
  let mut count := 0
  for (name, operations) in expected do
    let (rest, n) ← verifyOne name operations remaining
    remaining := rest
    count := count + n
  unless remaining.isEmpty do
    throw "unconsumed C release trace rows"
  if count != 16 then
    throw s!"C release trace row count drift: {count}"
  return count

end ReaderCReleaseAudit

open Lean Elab Command
run_cmd do
  let override ← liftIO <| IO.getEnv "LR_RELEASE_AUDIT"
  let path := override.getD "artifacts/lean-c-generated-heap/source-release-physical.tsv"
  let raw ← liftIO <| IO.FS.readFile path
  let lines := (raw.splitOn "\n").filter (· != "")
  let expectedHeader :=
    "case\tevent\toutcome\tparentRC\tchildRC\toldRC\tfreshRC\tchildField\tfreshPending\tchildBorrowed\tstampSlot\tparentId\tchildId\toldId\tfreshId"
  unless lines.headD "" == expectedHeader do
    throwError "C final-release trace header changed or missing"
  let parsed := (lines.drop 1).mapM ReaderCReleaseAudit.parse
  let .ok rows := parsed
    | throwError "C final-release trace parse refused: {repr parsed}"
  let checked := ReaderCReleaseAudit.verify rows
  let .ok count := checked
    | throwError "C final-release model refused: {repr checked}"
  logInfo m!"c_release_trace=PASS cases=3 rows={count} identities_and_last_ref_tombstones"
  logInfo m!"c_release_source_ledger=PASS cases=3 rows={count} per_checkpoint"

#print axioms ReaderCReleaseAudit.modeled_c_step_has_source
