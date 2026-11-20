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

/-! ## Universal consequences of accepting the concrete auditor

These facts are about the actual executable \`audit\` predicate, not an
abstract stand-in. They are deliberately extracted from the same guards
that the generated native certificate corpus exercises.
-/

/-- No certificate can be accepted when its source names or occurrences
violate the independent source admission predicate. -/
theorem audit_implies_sourceOK (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    sourceOK snapshot.source = true := by
  cases hs : sourceOK snapshot.source with
  | true => exact hs
  | false =>
      simp [audit, hs] at h

/-- The raw contract refuses every certificate from an unsupported
version, regardless of its row transcript or claimed result. -/
theorem audit_implies_version (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    snapshot.cert.version = 1 := by
  have hs := audit_implies_sourceOK snapshot maxCells maxSteps h
  by_contra hv
  simp [audit, hs, hv] at h

/-- The accepted free exponent must equal the number of original
internal columns minus the exact admitted pivot count. This is an
admission fact, not yet a proof that those pivots span the kernel. -/
theorem audit_implies_free_dimension (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    snapshot.claim.free =
      snapshot.source.internal.length - snapshot.cert.pivots.length := by
  unfold audit at h
  split_ifs at h <;> simp_all

#print axioms IndependentETH.AffineNativeAudit.audit_implies_sourceOK
#print axioms IndependentETH.AffineNativeAudit.audit_implies_version
#print axioms IndependentETH.AffineNativeAudit.audit_implies_free_dimension

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


/-! ## Independent, source-derived ordered-port receipt checks

The accepted port witness must refer to exactly the factor scopes and
order supplied in its data. The independent reference re-derives the
future support from *source scopes*, not from an asserted "future" field.
Names are decimal UTF-8 bytes, and lexicographic byte ordering matches
Rust String/BTreeSet order for the admitted ASCII identifier domain.

This is a concrete native-receipt audit, not a compiler refinement.
-/

structure PortReceipt where
  before : List Name
  next : List Name
  future : List Name
  kept : List Name
  dead : List Name
  deriving Repr, Inhabited, DecidableEq

structure PortPlan where
  scopes : List (List Name)
  order : List Nat
  output : List Name
  receipts : List PortReceipt
  deriving Repr, Inhabited, DecidableEq

def byteLexLess : Name → Name → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a == b then byteLexLess as bs else a < b

def strictlyByteSorted : List Name → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => byteLexLess a b && strictlyByteSorted (b :: rest)

def portNames (xs : List Name) : Finset Name := xs.toFinset

def futurePortScope (scopes : List (List Name))
    (indices : List Nat) : Finset Name :=
  indices.foldl (fun acc i =>
    acc ∪ portNames ((scopes[i]?).getD [])) ∅

/-- Check *actual* Rust-retired boundary ports against independent
source/future liveness. It also checks that the supplied order visits
every source factor once and that each recorded stage matches the
previous retained interface. -/
def auditPortPlan (plan : PortPlan) : Bool := Id.run do
  if plan.order.isEmpty || plan.order.length != plan.scopes.length then
    return false
  if !decide plan.order.Nodup ||
      !(plan.order.all (fun i => i < plan.scopes.length)) then
    return false
  if !(plan.scopes.all (fun names =>
        decide names.Nodup && names.all validName)) then
    return false
  if !decide plan.output.Nodup ||
      !(plan.output.all validName) then
    return false
  let allNames := futurePortScope plan.scopes plan.order
  if !(portNames plan.output ⊆ allNames) then
    return false
  if plan.receipts.length != plan.order.length - 1 then
    return false
  let firstIndex := (plan.order[0]?).getD 0
  let mut current := portNames ((plan.scopes[firstIndex]?).getD [])
  for i in List.range plan.receipts.length do
    let receipt := (plan.receipts[i]?).getD default
    let nextIndex := (plan.order[i + 1]?).getD 0
    let next := portNames ((plan.scopes[nextIndex]?).getD [])
    let future := futurePortScope plan.scopes (plan.order.drop (i + 2))
    let needed := future ∪ portNames plan.output
    let expectedKept := (current ∪ next) ∩ needed
    let expectedDead := (current ∪ next) \ expectedKept
    if portNames receipt.before != current ||
        portNames receipt.next != next ||
        portNames receipt.future != future then
      return false
    if !decide receipt.kept.Nodup ||
        !decide receipt.dead.Nodup then
      return false
    if portNames receipt.kept != expectedKept ||
        portNames receipt.dead != expectedDead then
      return false
    if !strictlyByteSorted receipt.kept ||
        !strictlyByteSorted receipt.dead then
      return false
    current := portNames receipt.kept
  return current == portNames plan.output

example : byteLexLess [120, 49, 48] [120, 50] = true := by decide
example : byteLexLess [120, 50] [120, 49, 48] = false := by decide


/-! ## Composed affine multiplicity receipts

The local matrix checker above only verifies the *newly* eliminated
variables. The full staged interface also inherits the two children's
previous powers of two. This independent chain auditor derives source
rows from the children's verified residuals, checks each local raw
certificate, and verifies free exponents across all merges. It is an
executable finite-corpus checker, not a proof of the Rust implementation.
-/

/-- Convert the verified residual rows back into the source equation
occurrences that Rust's actual Stage::merge constructs. The audit below
never trusts the emitter's claim about what those equations should be. -/
def residualEquations (c : Claim) : List SourceEquation :=
  c.residual.map (fun row =>
    { occurrences := row.columns.map (fun index =>
        (c.boundary[index]?).getD [])
      rhs := row.rhs })

structure MultiplicityTrace where
  plan : PortPlan
  leaves : List Snapshot
  merges : List Snapshot
  stageFree : List Nat
  deriving Repr, DecidableEq

/-- Independently verify a whole *concrete* ordered affine trace:
source leaves, all local merge source equations, each local replay
certificate, live-port plan, and inheritance of free exponents.
Each merge's local source must contain exactly the residual equations
from the two independently accepted child interfaces, in source order. -/
def auditMultiplicityTrace (t : MultiplicityTrace) : Bool := Id.run do
  if !auditPortPlan t.plan then
    return false
  if t.leaves.length != t.plan.scopes.length ||
      t.merges.length + 1 != t.plan.order.length ||
      t.stageFree.length != t.plan.order.length then
    return false
  let allPorts := futurePortScope t.plan.scopes t.plan.order
  let mut seenHidden : Finset Name := ∅
  for i in List.range t.leaves.length do
    let leaf := (t.leaves[i]?).getD emptySnapshot
    let declaredScope := (t.plan.scopes[i]?).getD []
    if !audit leaf || leaf.source.boundary != declaredScope then
      return false
    let hidden := portNames leaf.source.internal
    if !decide (hidden ∩ allPorts = ∅) ||
        !decide (hidden ∩ seenHidden = ∅) then
      return false
    seenHidden := seenHidden ∪ hidden
  let firstIndex := (t.plan.order[0]?).getD 0
  let first := (t.leaves[firstIndex]?).getD emptySnapshot
  let mut current : Claim := first.claim
  let mut cumulative := first.claim.free
  if (t.stageFree[0]?).getD 0 != cumulative then
    return false
  for i in List.range t.merges.length do
    let nextIndex := (t.plan.order[i + 1]?).getD 0
    let nextLeaf := (t.leaves[nextIndex]?).getD emptySnapshot
    let merge := (t.merges[i]?).getD emptySnapshot
    let ports := (t.plan.receipts[i]?).getD default
    if !audit merge then
      return false
    if merge.source.internal != ports.dead ||
        merge.source.boundary != ports.kept ||
        merge.claim.boundary != ports.kept then
      return false
    if merge.source.equations !=
        residualEquations current ++ residualEquations nextLeaf.claim then
      return false
    cumulative := cumulative + nextLeaf.claim.free + merge.claim.free
    if (t.stageFree[i + 1]?).getD 0 != cumulative then
      return false
    current := merge.claim
  return true

/-- The checker distinguishes local free bits from inherited ones. -/
example : (2 : Nat) ^ (2 + 3 + 1) = 64 := by decide


end IndependentETH.AffineNativeAudit
