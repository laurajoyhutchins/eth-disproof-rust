import Lean
import ReaderShellSimulation

/-!
# Validation of actual pinned Lean C physical-operation checkpoints

The C producer invokes real Lean 4.34.1 primitives and records the state
immediately afterwards. This Lean consumer checks every row against
ReaderShellSimulation.physicalStep and preserves parent/child/stamp pointer
identities *within the same allocation episode*.

The kernel theorem below states that a physical step matching the model
has a matching source step. What is NOT proved: that arbitrary C execution
produces correct/complete rows, or that the C runtime generally refines
the mathematical physicalStep definition. The C observations are bounded,
externally checked execution evidence, not premises manufactured in Lean.
-/

namespace ReaderShellTraceAudit

open ReaderShellSimulation

/-- Conditional, but generic: for any source state and admitted physical
step, the existing simulation theorem reconstructs its source successor. -/
theorem accepted_physical_step_has_source_step
    (s : Source) (i : Instruction) (p' : Physical)
    (h : physicalStep (represent s) i = some p') :
    ∃ s', sourceStep s i = some s' ∧ p' = represent s' := by
  rw [step_simulation] at h
  cases hs : sourceStep s i with
  | none => simp [hs] at h
  | some s' =>
      simp [hs] at h
      exact ⟨s', rfl, h.symm⟩

/-- An actual refused operation is represented as a rejection, never
as a secretly successful physical transition in the source model. -/
theorem rejected_physical_step_rejects_source
    (s : Source) (i : Instruction)
    (h : physicalStep (represent s) i = none) :
    sourceStep s i = none := by
  rw [step_simulation] at h
  cases hs : sourceStep s i with
  | none => rfl
  | some x => simp [hs] at h

structure Row where
  caseName : String
  event : String
  outcome : String
  physical : Physical
  parentId : Nat
  childId : Nat
  oldStampId : Nat
  deriving Repr

def number (field : String) : Except String Nat :=
  match field.toNat? with
  | some x => pure x
  | none => throw s!"invalid numeric field '{field}'"

def bit (field : String) : Except String Bool := do
  let n ← number field
  if n == 0 then pure false
  else if n == 1 then pure true
  else throw s!"invalid Boolean bit '{field}'"

def stampSlot : String → Except String StampSlot
  | "old" => pure .old
  | "spent" => pure .spent
  | "fresh" => pure .fresh
  | other => throw s!"unknown stamp slot '{other}'"

def parseRow (line : String) : Except String Row := do
  match line.splitOn "\t" with
  | [caseName, event, outcome, parent, child, stamp, field, borrowed, slot, unique, parentId, childId, stampId] =>
      let parentRC ← number parent
      let childRC ← number child
      let oldStampRC ← number stamp
      let childField ← bit field
      let borrowedChild ← bit borrowed
      let stampSlot ← stampSlot slot
      let observedUnique ← bit unique
      return {
        caseName, event, outcome
        physical := {
          parentRC, childRC, oldStampRC,
          childField, borrowedChild, stampSlot, observedUnique
        }
        parentId := (← number parentId)
        childId := (← number childId)
        oldStampId := (← number stampId)
      }
  | _ => throw s!"wrong number of TSV fields in '{line}'"

def instruction : String → Except String Instruction
  | "borrowChild" => pure .borrowChild
  | "inspectSharing" => pure .inspectSharing
  | "retainChild" => pure .retainChild
  | "retainParent" => pure .retainParent
  | "releaseSharedParent" => pure .releaseSharedParent
  | "stampDec" => pure .stampDec
  | "jumpOwned" => pure .jumpOwned
  | "setFreshStamp" => pure .setFreshStamp
  | "shellDel" => pure .shellDel
  | "releaseProjectedChild" => pure .releaseProjectedChild
  | x => throw s!"unknown source/physical instruction '{x}'"

def expected : List (String × List (String × String)) := [
  ("unique", [
    ("borrowChild", "ok"), ("inspectSharing", "ok"),
    ("stampDec", "ok"), ("jumpOwned", "ok"), ("shellDel", "ok")
  ]),
  ("shared", [
    ("retainParent", "ok"), ("inspectSharing", "ok"),
    ("releaseSharedParent", "ok"), ("borrowChild", "ok"),
    ("inspectSharing", "ok"), ("stampDec", "ok"),
    ("jumpOwned", "ok"), ("shellDel", "ok")
  ]),
  ("retained", [
    ("borrowChild", "ok"), ("inspectSharing", "ok"),
    ("stampDec", "ok"), ("retainChild", "ok"),
    ("shellDel", "refused")
  ]),
  ("fresh", [
    ("borrowChild", "ok"), ("inspectSharing", "ok"),
    ("stampDec", "ok"), ("jumpOwned", "ok"),
    ("setFreshStamp", "ok"), ("shellDel", "refused")
  ])
]

def sameIdentity (start next : Row) : Bool :=
  next.caseName == start.caseName &&
  next.parentId == start.parentId &&
  next.childId == start.childId &&
  next.oldStampId == start.oldStampId

/-- Replay the C transcript against the *existing proved physicalStep*.
The expected instruction order is independent of the C output; omitted,
extra, reordered or invented rows all fail closed. -/
def verifyEvents (start : Row) :
    List (String × String) → Physical → List Row →
      Except String (List Row × Nat)
  | [], _, rest => pure (rest, 0)
  | (event, outcome) :: steps, before, r :: rest => do
      if !sameIdentity start r || r.event != event || r.outcome != outcome then
        throw s!"event order/identity drift in case {start.caseName}: expected {event}/{outcome}, got {r.event}/{r.outcome}"
      let op ← instruction event
      let predicted := physicalStep before op
      if outcome == "ok" then
        if predicted != some r.physical then
          throw s!"physical transition mismatch in {start.caseName}/{event}: predicted {repr predicted}, measured {repr r.physical}"
      else if outcome == "refused" then
        if predicted != none || r.physical != before then
          throw s!"refusal changed physical state or model admitted it: {start.caseName}/{event}"
      else
        throw s!"unknown physical operation outcome '{outcome}'"
      let (tail, n) ← verifyEvents start steps r.physical rest
      pure (tail, n + 1)
  | _ :: _, _, [] =>
      throw s!"missing physical observation row after {start.caseName}"

def verifyOne (name : String) (ops : List (String × String))
    (rows : List Row) : Except String (List Row × Nat) := do
  match rows with
  | [] => throw s!"missing case '{name}'"
  | first :: rest =>
      if first.caseName != name || first.event != "initial" ||
         first.outcome != "start" then
        throw s!"missing initial row for case '{name}'"
      if first.parentId == 0 || first.childId == 0 ||
         first.oldStampId == 0 ||
         first.parentId == first.childId ||
         first.parentId == first.oldStampId ||
         first.childId == first.oldStampId then
        throw s!"aliased or null physical identities in '{name}'"
      if first.physical.oldStampRC < 2 then
        throw s!"old heap stamp lacked a protected external source credit in '{name}'"
      let external := first.physical.oldStampRC - 1
      if first.physical != represent (initial external) then
        throw s!"initial physical allocation inconsistent with source representation: {name}"
      let (tail, n) ← verifyEvents first ops first.physical rest
      pure (tail, n + 1)

def verify : List Row → Except String Nat
  | rows => do
      let mut rest := rows
      let mut total := 0
      for (name, ops) in expected do
        let (tail, n) ← verifyOne name ops rest
        rest := tail
        total := total + n
      if !rest.isEmpty then
        throw "unconsumed physical rows after expected experiments"
      if total != 28 then
        throw s!"physical row count drift: expected 28, got {total}"
      pure total

end ReaderShellTraceAudit

open Lean Elab Command

run_cmd do
  let raw ← liftIO <| IO.FS.readFile "artifacts/lean-c-generated-heap/source-shell-physical.tsv"
  let lines := raw.splitOn "\n" |>.filter (· != "")
  let expectedHeader :=
    "case\tevent\toutcome\tparentRC\tchildRC\toldStampRC\tchildField\tborrowedChild\tstampSlot\tobservedUnique\tparentId\tchildId\toldStampId"
  let header := lines.headD ""
  unless header == expectedHeader do
    throwError "Source C physical trace header changed or missing"
  let parsed := (lines.drop 1).mapM ReaderShellTraceAudit.parseRow
  let .ok rows := parsed
    | throwError "Source C physical trace parse refused: {repr parsed}"
  let .ok count := ReaderShellTraceAudit.verify rows
    | throwError "Source C physical trace refinement refused: {repr (ReaderShellTraceAudit.verify rows)}"
  logInfo m!"source-shell-physical-trace=PASS rows={count} cases=4 complete-order-and-identity"

#print axioms ReaderShellTraceAudit.accepted_physical_step_has_source_step
#print axioms ReaderShellTraceAudit.rejected_physical_step_rejects_source
