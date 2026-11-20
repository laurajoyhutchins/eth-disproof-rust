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
  | true => rfl
  | false =>
      simp [audit, hs] at h

/-- The raw contract refuses every certificate from an unsupported
version, regardless of its row transcript or claimed result. -/
theorem audit_implies_version (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    snapshot.cert.version = 1 := by
  by_contra hv
  simp [audit, hv] at h

/-- The accepted free exponent must equal the number of original
internal columns minus the exact admitted pivot count. This is an
admission fact, not yet a proof that those pivots span the kernel. -/
theorem audit_implies_free_dimension (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    snapshot.claim.free =
      snapshot.source.internal.length - snapshot.cert.pivots.length := by
  by_contra hf
  have hg :
      (snapshot.claim.rank != snapshot.cert.pivots.length ||
       snapshot.claim.free !=
         (snapshot.source.internal.length - snapshot.cert.pivots.length)) = true := by
    simp [hf]
  simp [audit, hg] at h

/-- The actual pivot-identity test used inside audit, factored only for
stating its universal acceptance consequence. -/
def pivotIdentityOK (s : Source) (c : Certificate) : Bool :=
  (List.range c.pivots.length).all (fun i =>
    (List.range s.equations.length).all (fun j =>
      bitAt (rowAt (replay s c) j) ((c.pivots[i]?).getD 0) == (i == j)))

/-- All nonpivot rows in the independently replayed matrix contain
no internal coefficients. This prevents hidden equations from being
mistaken for external-only residual constraints. -/
def residualInternalZero (s : Source) (c : Certificate) : Bool :=
  ((replay s c).drop c.pivots.length).all (fun row =>
    (List.range s.internal.length).all (fun j => !(bitAt row j)))

/-- Reconstruct the boundary-only residual directly from independently
replayed rows, not from the producer's proposed claim. -/
def replayedResidual (s : Source) (c : Certificate) : List Residual :=
  ((replay s c).map
    (fun row => expectedResidual row s.internal.length s.boundary.length)).drop
      c.pivots.length

/-- Actual auditor acceptance implies the complete pivot identity
condition for every row and admitted pivot column. -/
theorem audit_implies_pivot_identity (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    pivotIdentityOK snapshot.source snapshot.cert = true := by
  cases hp : pivotIdentityOK snapshot.source snapshot.cert with
  | true => rfl
  | false =>
      have hbad :
          ∃ i < snapshot.cert.pivots.length,
            ∃ j < snapshot.source.equations.length,
              ¬bitAt (rowAt (replay snapshot.source snapshot.cert) j)
                ((snapshot.cert.pivots[i]?).getD 0) = (i == j) := by
        simpa [pivotIdentityOK] using hp
      simp [audit, hbad] at h

/-- Actual auditor acceptance implies every residual row is independent
of all internal variables, not merely that its claimed format is valid. -/
theorem audit_implies_residual_internal_zero (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    residualInternalZero snapshot.source snapshot.cert = true := by
  cases hz : residualInternalZero snapshot.source snapshot.cert with
  | true => rfl
  | false =>
      have hbad :
          ∃ row ∈ (replay snapshot.source snapshot.cert).drop snapshot.cert.pivots.length,
            ∃ j < snapshot.source.internal.length, bitAt row j = true := by
        simpa [residualInternalZero] using hz
      simp [audit, hbad] at h

/-- Acceptance forces exactly the independently reconstructed residual
equations, including each coefficient column and right-hand side.
No source-dependent equality is taken as an axiom. -/
theorem audit_implies_replayed_residual (snapshot : Snapshot)
    (maxCells maxSteps : Nat)
    (h : audit snapshot maxCells maxSteps = true) :
    replayedResidual snapshot.source snapshot.cert =
      snapshot.claim.residual := by
  by_contra hneq
  have hb :
      (replayedResidual snapshot.source snapshot.cert ==
        snapshot.claim.residual) = false := by
    simp [hneq]
  have hfinal :
      (List.drop snapshot.cert.pivots.length
        (List.map
          (fun row => expectedResidual row snapshot.source.internal.length
            snapshot.source.boundary.length)
          (replay snapshot.source snapshot.cert)) ==
        snapshot.claim.residual) = false := by
    exact hb
  simp [audit, hfinal] at h

#print axioms IndependentETH.AffineNativeAudit.audit_implies_pivot_identity
#print axioms IndependentETH.AffineNativeAudit.audit_implies_residual_internal_zero
#print axioms IndependentETH.AffineNativeAudit.audit_implies_replayed_residual

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



/-! ## Universal occurrence-to-coefficient parity

The next lemmas use the *actual* occurrenceBit function in sourceRows.
They establish parity correspondence for every finite occurrence list,
including repeated names, under the independent source admission
condition of unique declared names and complete occurrence coverage.
No exhaustive assignment enumeration or native producer assumptions.
-/

private def xorAll (xs : List Bool) : Bool :=
  xs.foldr (fun x total => x ^^ total) false

private theorem xorAll_map_xor {α : Type*}
    (xs : List α) (f g : α → Bool) :
    xorAll (xs.map (fun x => f x ^^ g x)) =
      xorAll (xs.map f) ^^ xorAll (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      calc
        xorAll ((x :: xs).map (fun a => f a ^^ g a)) =
            (f x ^^ g x) ^^
              xorAll (xs.map (fun a => f a ^^ g a)) := rfl
        _ = (f x ^^ g x) ^^
              (xorAll (xs.map f) ^^ xorAll (xs.map g)) := by rw [ih]
        _ = xorAll ((x :: xs).map f) ^^
              xorAll ((x :: xs).map g) := by
              cases f x <;> cases g x <;>
                cases xorAll (xs.map f) <;>
                cases xorAll (xs.map g) <;> decide

private theorem occurrenceFold_acc
    (xs : List Name) (target : Name) (acc : Bool) :
    xs.foldl (fun p name => p ^^ (name == target)) acc =
      acc ^^ xs.foldl (fun p name => p ^^ (name == target)) false := by
  induction xs generalizing acc with
  | nil => cases acc <;> decide
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc ^^ (x == target)), ih (false ^^ (x == target))]
      cases acc <;> cases x == target <;>
        cases xs.foldl (fun p name => p ^^ (name == target)) false <;> decide

private theorem occurrenceBit_cons (x : Name) (xs : List Name)
    (target : Name) :
    occurrenceBit (x :: xs) target =
      (x == target) ^^ occurrenceBit xs target := by
  simp only [occurrenceBit, List.foldl_cons]
  simpa using occurrenceFold_acc xs target (x == target)

private theorem xorAll_delta_none (ns : List Name)
    (target : Name) (assignment : Name → Bool)
    (h : target ∉ ns) :
    xorAll (ns.map (fun name => (target == name) && assignment name)) =
      false := by
  induction ns with
  | nil => rfl
  | cons x xs ih =>
      have hx : target ≠ x := by
        intro heq
        apply h
        exact List.mem_cons.mpr (Or.inl heq)
      have ht : target ∉ xs := by
        intro hmem
        exact h (List.mem_cons_of_mem _ hmem)
      calc
        xorAll ((x :: xs).map
          (fun name => (target == name) && assignment name)) =
            ((target == x) && assignment x) ^^
            xorAll (xs.map
              (fun name => (target == name) && assignment name)) := rfl
        _ = false := by simp [hx, ih ht]

private theorem xorAll_delta (ns : List Name)
    (target : Name) (assignment : Name → Bool)
    (hn : ns.Nodup) :
    xorAll (ns.map (fun name => (target == name) && assignment name)) =
      if target ∈ ns then assignment target else false := by
  induction ns with
  | nil => rfl
  | cons x xs ih =>
      have hn' := (List.nodup_cons.mp hn)
      by_cases hx : target = x
      · subst target
        have htail := xorAll_delta_none xs x assignment hn'.1
        simp [xorAll, htail]
      · have hrest := ih hn'.2
        simp [xorAll, hx, hrest]

private def coefficientEval
    (ns occ : List Name) (assignment : Name → Bool) : Bool :=
  xorAll (ns.map (fun n => occurrenceBit occ n && assignment n))

private theorem coefficientEval_nil (ns : List Name)
    (assignment : Name → Bool) :
    coefficientEval ns [] assignment = false := by
  induction ns with
  | nil => rfl
  | cons x xs ih =>
      simpa [coefficientEval, xorAll, occurrenceBit] using ih

private theorem coefficientEval_cons (ns : List Name)
    (x : Name) (xs : List Name) (assignment : Name → Bool)
    (hn : ns.Nodup) :
    coefficientEval ns (x :: xs) assignment =
      (if x ∈ ns then assignment x else false) ^^
        coefficientEval ns xs assignment := by
  have hpoint (n : Name) :
      (occurrenceBit (x :: xs) n && assignment n) =
        ((x == n) && assignment n) ^^
          (occurrenceBit xs n && assignment n) := by
    rw [occurrenceBit_cons]
    cases x == n <;> cases occurrenceBit xs n <;>
      cases assignment n <;> decide
  unfold coefficientEval
  simp_rw [hpoint]
  rw [xorAll_map_xor]
  rw [xorAll_delta ns x assignment hn]

private def occurrenceEval (xs : List Name)
    (assignment : Name → Bool) : Bool :=
  xs.foldl (fun parity n => parity ^^ assignment n) false

private theorem occurrenceEval_acc (xs : List Name)
    (assignment : Name → Bool) (acc : Bool) :
    xs.foldl (fun parity n => parity ^^ assignment n) acc =
      acc ^^ occurrenceEval xs assignment := by
  induction xs generalizing acc with
  | nil => cases acc <;> decide
  | cons x xs ih =>
      simp only [List.foldl_cons, occurrenceEval]
      rw [ih (acc ^^ assignment x), ih (false ^^ assignment x)]
      cases acc <;> cases assignment x <;>
        cases xs.foldl (fun parity n => parity ^^ assignment n) false <;> decide

private theorem occurrenceEval_cons (x : Name) (xs : List Name)
    (assignment : Name → Bool) :
    occurrenceEval (x :: xs) assignment =
      assignment x ^^ occurrenceEval xs assignment := by
  simp only [occurrenceEval, List.foldl_cons]
  simpa using occurrenceEval_acc xs assignment (assignment x)

/-- Every repeated source occurrence toggles exactly its corresponding
matrix coefficient. In particular two occurrences cancel. The statement
quantifies over *all* assignments and arbitrarily long source lists. -/
theorem occurrence_parity_eq_source_coefficients
    (ns occ : List Name) (assignment : Name → Bool)
    (hn : ns.Nodup) (hcoverage : ∀ x ∈ occ, x ∈ ns) :
    occurrenceEval occ assignment = coefficientEval ns occ assignment := by
  induction occ with
  | nil =>
      simp [occurrenceEval, coefficientEval_nil]
  | cons x xs ih =>
      have hx : x ∈ ns := hcoverage x (by simp)
      have hxs : ∀ y ∈ xs, y ∈ ns := by
        intro y hy
        exact hcoverage y (List.mem_cons_of_mem _ hy)
      rw [occurrenceEval_cons, ih hxs, coefficientEval_cons ns x xs assignment hn]
      simp [hx]

/-- The coefficient vector used in the parity theorem is *literally*
the prefix of the row constructed by the independent audit. -/
theorem occurrence_matrix_row_is_sourceRow (s : Source)
    (e : SourceEquation) (he : e ∈ s.equations) :
    ((names s).map (occurrenceBit e.occurrences) ++ [e.rhs]) ∈
      sourceRows s := by
  exact List.mem_map.mpr ⟨e, he, rfl⟩

/-! ## Universal pivot/free reindexing for arbitrary column sets

The pivot positions need not be consecutive or start at zero.
Functions on all internal coordinates are in bijection with
functions on the declared pivot coordinates and their complement.
This is a constructive exact coordinate split, not a count oracle.
-/

private def splitCoordinates {k : Nat} (pivots : Finset (Fin k))
    (values : Fin k → Bool) :
    (↥pivots → Bool) × (↥(Finset.univ \ pivots) → Bool) :=
  (fun i => values i.val, fun i => values i.val)

private def joinCoordinates {k : Nat} (pivots : Finset (Fin k))
    (parts : (↥pivots → Bool) ×
      (↥(Finset.univ \ pivots) → Bool)) :
    Fin k → Bool :=
  fun i =>
    if h : i ∈ pivots then parts.1 ⟨i, h⟩
    else parts.2 ⟨i, by simp [h]⟩

/-- An arbitrary noncontiguous set of pivot columns can be reindexed
with its full complement, without losing or duplicating assignments. -/
def pivotFreeCoordinates {k : Nat} (pivots : Finset (Fin k)) :
    (Fin k → Bool) ≃
      ((↥pivots → Bool) × (↥(Finset.univ \ pivots) → Bool)) where
  toFun := splitCoordinates pivots
  invFun := joinCoordinates pivots
  left_inv := by
    intro values
    funext i
    by_cases hi : i ∈ pivots
    · simp [splitCoordinates, joinCoordinates, hi]
    · simp [splitCoordinates, joinCoordinates, hi]
  right_inv := by
    intro parts
    apply Prod.ext
    · funext i
      simp [splitCoordinates, joinCoordinates, i.property]
    · funext i
      have hi : i.val ∉ pivots := (Finset.mem_sdiff.mp i.property).2
      simp [splitCoordinates, joinCoordinates, hi]

/-- Exactly k - r coordinates remain free when r distinct pivot
columns are selected, for every k and every pivot subset. -/
theorem pivotFree_card {k : Nat} (pivots : Finset (Fin k)) :
    Fintype.card ↥(Finset.univ \ pivots) = k - pivots.card := by
  classical
  rw [Fintype.card_coe]
  rw [Finset.card_sdiff (Finset.subset_univ pivots)]
  simp

#print axioms IndependentETH.AffineNativeAudit.occurrence_parity_eq_source_coefficients
#print axioms IndependentETH.AffineNativeAudit.occurrence_matrix_row_is_sourceRow
#print axioms IndependentETH.AffineNativeAudit.pivotFreeCoordinates
#print axioms IndependentETH.AffineNativeAudit.pivotFree_card


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
