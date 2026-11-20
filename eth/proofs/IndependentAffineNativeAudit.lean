import Mathlib

/-!
# Independent executable Lean audit of native affine receipts

Rust emits a data-only Lean term describing source name bytes,
XOR equation occurrences, raw row-operation steps, pivots and
the claimed interface. The reference rebuilds rows, replays steps
and verifies acceptance independently of the Rust checker.

Generated examples use the Lean decide tactic: their conclusions
are kernel-checked propositions for actual Rust-emitted data.
This is finite cross-implementation evidence, NOT an all-input
Rust-to-Lean refinement theorem.
-/

-- Concrete source-byte lists may contain more than 128 variables; these
-- limits apply to fixture checking, not to native algorithm resources.
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace IndependentETH.AffineNativeAudit

abbrev Name := List Nat

structure SourceEquation where
  occurrences : List Name
  rhs : Bool
  deriving Repr, DecidableEq

structure Source where
  internal : List Name
  boundary : List Name
  equations : List SourceEquation
  deriving Repr, DecidableEq

structure Step where
  tag : Nat
  first : Nat
  second : Nat
  deriving Repr, DecidableEq

structure Certificate where
  version : Nat
  steps : List Step
  pivots : List Nat
  deriving Repr, DecidableEq

structure Residual where
  columns : List Nat
  rhs : Bool
  deriving Repr, DecidableEq

structure Claim where
  boundary : List Name
  residual : List Residual
  rank : Nat
  free : Nat
  xors : Nat
  deriving Repr, DecidableEq

structure Snapshot where
  source : Source
  cert : Certificate
  claim : Claim
  deriving Repr, DecidableEq

def names (s : Source) : List Name := s.internal ++ s.boundary

/-- The same *source-domain contract* as native Rust:
a nonempty ASCII letter followed by ASCII letters, digits or underscore.
The independent Lean auditor checks bytes, not Rust Unicode chars. -/
def asciiLetter (byte : Nat) : Bool :=
  decide ((65 ≤ byte ∧ byte ≤ 90) ∨ (97 ≤ byte ∧ byte ≤ 122))

def asciiDigit (byte : Nat) : Bool :=
  decide (48 ≤ byte ∧ byte ≤ 57)

def validName : Name → Bool
  | [] => false
  | first :: rest =>
      asciiLetter first &&
        rest.all (fun byte =>
          asciiLetter byte || asciiDigit byte || byte == 95)

def sourceOK (s : Source) : Bool :=
  let ns := names s
  decide ns.Nodup &&
    ns.all validName &&
    s.equations.all (fun e => e.occurrences.all (fun n => ns.contains n))

theorem sourceOK_names_valid (s : Source)
    (h : sourceOK s = true) :
    (names s).all validName = true := by
  simp only [sourceOK, Bool.and_eq_true] at h
  exact h.1.2

example : validName [117, 95, 49] = true := by decide
example : validName [95, 117] = false := by decide
example : validName [49, 117] = false := by decide
example : validName [117, 45, 118] = false := by decide
example : validName [195, 169] = false := by decide

/-- Each occurrence toggles the source coefficient, including repeats. -/
def occurrenceBit (occurrences : List Name) (name : Name) : Bool :=
  occurrences.foldl (fun parity v => parity ^^ (v == name)) false

def sourceRows (s : Source) : List (List Bool) :=
  s.equations.map (fun e =>
    (names s).map (occurrenceBit e.occurrences) ++ [e.rhs])

def bitAt (row : List Bool) (index : Nat) : Bool :=
  (row[index]?).getD false

def rowAt (rows : List (List Bool)) (index : Nat) : List Bool :=
  (rows[index]?).getD []

def validStep (m : Nat) (step : Step) : Bool :=
  (step.tag == 0 || step.tag == 1) &&
  step.first < m && step.second < m &&
  step.first != step.second

def applyStep (rows : List (List Bool)) (step : Step) : List (List Bool) :=
  let first := rowAt rows step.first
  let second := rowAt rows step.second
  (List.range rows.length).map (fun i =>
    if step.tag == 0 then
      if i == step.first then second
      else if i == step.second then first
      else rowAt rows i
    else if i == step.first then List.zipWith (· ^^ ·) first second
    else rowAt rows i)

def replay (s : Source) (c : Certificate) : List (List Bool) :=
  c.steps.foldl applyStep (sourceRows s)

def strictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && strictlyIncreasing (b :: rest)

def expectedResidual (row : List Bool) (k b : Nat) : Residual :=
  { columns := (List.range b).filter (fun j => bitAt row (k + j))
    rhs := bitAt row (k + b) }

/-- Independent acceptance predicate on raw certificate values. -/
def audit (snapshot : Snapshot) (maxCells maxSteps : Nat := 8000000) : Bool := Id.run do
  let s := snapshot.source
  let c := snapshot.cert
  let claimed := snapshot.claim
  let k := s.internal.length
  let b := s.boundary.length
  let m := s.equations.length
  let r := c.pivots.length
  if !sourceOK s then return false
  if c.version != 1 then return false
  if c.steps.length > maxSteps || m * (k + b + 1) > maxCells then return false
  if !c.steps.all (validStep m) then return false
  if !strictlyIncreasing c.pivots || !(c.pivots.all (· < k)) then return false
  if r > k || r > m then return false
  if claimed.boundary != s.boundary then return false
  if claimed.rank != r || claimed.free != k - r then return false
  if claimed.xors != (c.steps.filter (fun x => x.tag == 1)).length then return false
  let rows := replay s c
  if !(List.range r).all (fun i =>
       (List.range m).all (fun j =>
         bitAt (rowAt rows j) (c.pivots[i]?.getD 0) == (i == j))) then
    return false
  -- Residual rows have no internal coefficients; pivot rows can have
  -- free-column coefficients.
  if !(rows.drop r).all (fun row =>
       (List.range k).all (fun j => !(bitAt row j))) then
    return false
  let residual := (rows.drop r).map (fun row => expectedResidual row k b)
  return residual == claimed.residual

/-- Independent source-name Boolean XOR oracle on small examples. -/
def namedBit : List Name → List Bool → Name → Bool
  | [], _, _ => false
  | _, [], _ => false
  | n :: ns, b :: bs, target =>
      if n == target then b else namedBit ns bs target

def satisfiesSource (s : Source) (internal boundary : List Bool) : Bool :=
  let ns := names s
  let bits := internal ++ boundary
  s.equations.all (fun e =>
    (e.occurrences.foldl
      (fun parity name => parity ^^ namedBit ns bits name) false) == e.rhs)

def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      ((allBits n).map (false :: ·)) ++ ((allBits n).map (true :: ·))

def directCount (s : Source) (boundary : List Bool) : Nat :=
  ((allBits s.internal.length).filter
    (fun internal => satisfiesSource s internal boundary)).length

def claimedCount (c : Claim) (boundary : List Bool) : Nat :=
  if c.residual.all (fun row =>
    (row.columns.foldl
      (fun parity index => parity ^^ bitAt boundary index) false) == row.rhs) then
    2 ^ c.free
  else 0

/-- All boundary assignments are exhaustively counted from source XOR
occurrences; this is deliberately only used for small emitted examples. -/
def exhaustiveAgreement (snap : Snapshot) : Bool :=
  (allBits snap.source.boundary.length).all (fun boundary =>
    directCount snap.source boundary == claimedCount snap.claim boundary)

def emptySnapshot : Snapshot :=
  { source := { internal := [], boundary := [], equations := [] }
    cert := { version := 1, steps := [], pivots := [] }
    claim := { boundary := [], residual := [], rank := 0, free := 0, xors := 0 } }

example : audit emptySnapshot = true := by decide
example : exhaustiveAgreement emptySnapshot = true := by decide

#print axioms IndependentETH.AffineNativeAudit.sourceOK_names_valid

end IndependentETH.AffineNativeAudit
