import Mathlib

/-!
# A connected non-affine CNF family: exact finite-state semantics

For a list of parity right-hand sides d, a three-bit seed determines all
variables by the recurrence x_(i+3) = x_i xor x_(i+1) xor d_i.
Each parity equation has a four-clause, assignment-preserving 3-CNF gadget.

The additional positive sliding-window clauses reject the zero three-bit
window. We prove that the resulting *seed-level* formula is identical at
every seed to a finite forbidden-state mask and that for homogeneous RHS
the count is seven, for every recurrence length.

This is a restricted family, not a theorem about arbitrary CNF, and not
a formal refinement of the separate Rust CSR recognizer.
-/

namespace IndependentETH.NonAffine

abbrev State := Bool × Bool × Bool

def zeroState : State := (false, false, false)

def next (d : Bool) : State → State
  | (a, b, c) => (b, c, Bool.xor (Bool.xor a b) d)

def previous (d : Bool) : State → State
  | (b, c, w) => (Bool.xor (Bool.xor w b) d, b, c)

theorem previous_next (d : Bool) (s : State) :
    previous d (next d s) = s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem next_previous (d : Bool) (s : State) :
    next d (previous d s) = s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Exact satisfaction of the four clauses forbidding odd-parity triples. -/
def evenGadget (a b c : Bool) : Bool :=
  (a || b || !c) &&
  (a || !b || c) &&
  (!a || b || c) &&
  (!a || !b || !c)

/-- Exact satisfaction of the four clauses forbidding even-parity triples. -/
def oddGadget (a b c : Bool) : Bool :=
  (a || b || c) &&
  (a || !b || !c) &&
  (!a || b || !c) &&
  (!a || !b || c)

def parityGadget (d a b c : Bool) : Bool :=
  if d then oddGadget a b c else evenGadget a b c

theorem gadget_exact (d a b c : Bool) :
    parityGadget d a b c =
      decide (Bool.xor (Bool.xor a b) c = d) := by
  cases d <;> cases a <;> cases b <;> cases c <;> decide

/-- The Boolean OR on three ports is exactly nonzeroness of their state. -/
def nonzero (s : State) : Bool := decide (s ≠ zeroState)

def orWindow : State → Bool
  | (a, b, c) => a || b || c

theorem orWindow_exact (s : State) : orWindow s = nonzero s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

/-- Enforce every sliding OR window, including the last window. -/
def accepts : State → List Bool → Bool
  | s, [] => nonzero s
  | s, d :: ds => nonzero s && accepts (next d s) ds

/-- The forbidden mask is a set of at most eight states, *not* a table
    of assignments to every original variable. -/
def forbidden (ds : List Bool) : Finset State :=
  Finset.univ.filter (fun s => accepts s ds = false)

def accepted (ds : List Bool) : Finset State :=
  Finset.univ.filter (fun s => accepts s ds = true)

/-- The mask is extensionally equivalent to the whole recurrence/OR
    evaluation at every externally visible initial state. -/
theorem accepted_iff_not_forbidden (ds : List Bool) (s : State) :
    accepts s ds = true ↔ s ∉ forbidden ds := by
  simp only [forbidden, Finset.mem_filter, Finset.mem_univ, true_and]
  cases accepts s ds <;> simp

theorem accepted_complement (ds : List Bool) :
    accepted ds = (forbidden ds)ᶜ := by
  ext s
  simpa [accepted] using (accepted_iff_not_forbidden ds s)

/-- In the semantic seed space there are eight possible inputs; the
    exact number of satisfying assignments is 8 minus forbidden seeds. -/
theorem count_eq_eight_sub_forbidden (ds : List Bool) :
    (accepted ds).card = 8 - (forbidden ds).card := by
  rw [accepted_complement]
  simp [Finset.card_compl, Fintype.card_prod]

def zeros : Nat → List Bool
  | 0 => []
  | k + 1 => false :: zeros k

theorem nonzero_next_false (s : State) :
    nonzero (next false s) = nonzero s := by
  rcases s with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;> decide

theorem accepts_zeros (k : Nat) (s : State) :
    accepts s (zeros k) = nonzero s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      change (nonzero s && accepts (next false s) (zeros k)) = nonzero s
      rw [ih, nonzero_next_false]
      cases nonzero s <;> rfl

/-- The homogeneous connected non-affine family has seven satisfying
    three-bit seeds at *every* size n=k+3 (with k>=1 for 3-CNF). By the recurrence, each seed
    has exactly one corresponding n-bit assignment. -/
theorem homogeneous_count_seven (k : Nat) :
    (accepted (zeros k)).card = 7 := by
  have h : accepted (zeros k) =
      (Finset.univ : Finset State).filter (fun s => s ≠ zeroState) := by
    ext s
    simp [accepted, accepts_zeros, nonzero]
  rw [h]
  decide

/-! ## Signed clause-row semantics and a complete source certificate

A three-literal signed row is represented by its *unique falsifying*
assignment on three ordered variable columns. For a DIMACS literal, the
falsifying bit is false for a positive literal and true for a negative
literal. This model retains all three columns and every row; it does not
rely on SAT-equivalence-preserving preprocessing or a guessed subgraph.
-/

structure SignedRow where
  first : Nat
  second : Nat
  third : Nat
  falsifiesAt : State
deriving DecidableEq

def row (i j k : Nat) (p : State) : SignedRow :=
  ⟨i, j, k, p⟩

def tripleAt (x : Nat → Bool) (i j k : Nat) : State :=
  (x i, x j, x k)

def rowHolds (x : Nat → Bool) (r : SignedRow) : Prop :=
  tripleAt x r.first r.second r.third ≠ r.falsifiesAt

def allRowsHold (x : Nat → Bool) (rows : Finset SignedRow) : Prop :=
  ∀ r ∈ rows, rowHolds x r

def parityState : State → Bool
  | (a, b, c) => Bool.xor (Bool.xor a b) c

def parityMask (d : Bool) : Finset State :=
  Finset.univ.filter (fun p => parityState p ≠ d)

theorem avoid_mask_iff_not_mem (mask : Finset State) (s : State) :
    (∀ p ∈ mask, s ≠ p) ↔ s ∉ mask := by
  constructor
  · intro h hs
    exact (h s hs) rfl
  · intro h p hp heq
    apply h
    simpa [heq] using hp

theorem parityMask_exact (d : Bool) (s : State) :
    (∀ p ∈ parityMask d, s ≠ p) ↔ parityState s = d := by
  rw [avoid_mask_iff_not_mem]
  simp [parityMask]

def parityRows (i : Nat) (d : Bool) : Finset SignedRow :=
  (parityMask d).image (fun p => row i (i + 1) (i + 3) p)

def windowRow (i : Nat) : SignedRow :=
  row i (i + 1) (i + 2) zeroState

theorem parityRows_exact (x : Nat → Bool) (i : Nat) (d : Bool) :
    (∀ r ∈ parityRows i d, rowHolds x r) ↔
      parityState (tripleAt x i (i + 1) (i + 3)) = d := by
  constructor
  · intro h
    apply (parityMask_exact d (tripleAt x i (i + 1) (i + 3))).mp
    intro p hp
    exact h (row i (i + 1) (i + 3) p)
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  · intro h r hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
    exact (parityMask_exact d (tripleAt x i (i + 1) (i + 3))).mpr h p hp

/-- Exactly the signed rows of the recurrence family, as a finite set.
No row order is imposed, but duplicate rows are irrelevant to CNF semantics.
The associated Rust CSR reader enforces nonduplication independently. -/
def sourceRows (ds : List Bool) : Finset SignedRow :=
  (Finset.range ds.length).biUnion (fun i => parityRows i (ds[i]!)) ∪
    (Finset.range (ds.length + 1)).image windowRow

/-- An independent, all-assignment description of the *whole* signed source.
Unlike a seed-only theorem, this states exactly what a certified row set
means for any valuation of the declared variables. -/
theorem sourceRows_exact (ds : List Bool) (x : Nat → Bool) :
    allRowsHold x (sourceRows ds) ↔
      (∀ i, i < ds.length →
        parityState (tripleAt x i (i + 1) (i + 3)) = ds[i]!) ∧
      (∀ i, i < ds.length + 1 →
        tripleAt x i (i + 1) (i + 2) ≠ zeroState) := by
  constructor
  · intro h
    constructor
    · intro i hi
      apply (parityRows_exact x i (ds[i]!)).mp
      intro r hr
      exact h r (Finset.mem_union.mpr
        (Or.inl (Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_range.mpr hi, hr⟩)))
    · intro i hi
      exact h (windowRow i) (Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr
          ⟨i, Finset.mem_range.mpr hi, rfl⟩)))
  · rintro ⟨hp, ho⟩ r hr
    rcases Finset.mem_union.mp hr with parity | window
    · obtain ⟨i, hi, hrow⟩ := Finset.mem_biUnion.mp parity
      exact (parityRows_exact x i (ds[i]!)).mpr
        (hp i (Finset.mem_range.mp hi)) r hrow
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp window
      exact ho i (Finset.mem_range.mp hi)

/-- Executable semantic acceptance predicate for the complete row source,
rather than a sampled valuation or an inferred partial gadget. -/
def checkSourceRows (actual : Finset SignedRow) (ds : List Bool) : Bool :=
  decide (actual = sourceRows ds)

/-- A positive source-row equality check certifies the interpretation
of *all* rows, for *all* Boolean valuations. -/
theorem checked_source_rows_exact
    (actual : Finset SignedRow) (ds : List Bool) (x : Nat → Bool)
    (h : checkSourceRows actual ds = true) :
    allRowsHold x actual ↔
      (∀ i, i < ds.length →
        parityState (tripleAt x i (i + 1) (i + 3)) = ds[i]!) ∧
      (∀ i, i < ds.length + 1 →
        tripleAt x i (i + 1) (i + 2) ≠ zeroState) := by
  have hrows : actual = sourceRows ds := of_decide_eq_true h
  rw [hrows]
  exact sourceRows_exact ds x

/-! ## Signed literal polarity is exactly the unique falsifying tuple. -/

/-- Interpret a three-literal signed clause: true means its literal is
negated. This is the same polarity convention used by signed CSR, where
a negative literal is stored as -1. -/
def signedClauseEval : State → State → Bool
  | (a, b, c), (negativeA, negativeB, negativeC) =>
      (if negativeA then !a else a) ||
      (if negativeB then !b else b) ||
      (if negativeC then !c else c)

/-- Every signed three-literal clause fails at exactly one local tuple:
the tuple of its three negative-literal flags. -/
theorem signedClause_exact (s polarity : State) :
    signedClauseEval s polarity = true ↔ s ≠ polarity := by
  rcases s with ⟨a, b, c⟩
  rcases polarity with ⟨p, q, r⟩
  cases a <;> cases b <;> cases c <;>
    cases p <;> cases q <;> cases r <;> decide

theorem rawRows_equiv_rowHolds (x : Nat → Bool) (rows : Finset SignedRow) :
    (∀ r ∈ rows,
      signedClauseEval (tripleAt x r.first r.second r.third)
        r.falsifiesAt = true) ↔ allRowsHold x rows := by
  constructor
  · intro h r hr
    exact (signedClause_exact _ _).mp (h r hr)
  · intro h r hr
    exact (signedClause_exact _ _).mpr (h r hr)

/-- Acceptance implies that evaluating every actual signed row is exactly
the full recurrence constraint semantics, for every source assignment.
The raw CSR byte-to-row decoding is not proved by this theorem. -/
theorem checked_signed_cnf_exact
    (actual : Finset SignedRow) (ds : List Bool) (x : Nat → Bool)
    (h : checkSourceRows actual ds = true) :
    (∀ r ∈ actual,
      signedClauseEval (tripleAt x r.first r.second r.third)
        r.falsifiesAt = true) ↔
      (∀ i, i < ds.length →
        parityState (tripleAt x i (i + 1) (i + 3)) = ds[i]!) ∧
      (∀ i, i < ds.length + 1 →
        tripleAt x i (i + 1) (i + 2) ≠ zeroState) := by
  rw [rawRows_equiv_rowHolds]
  exact checked_source_rows_exact actual ds x h

#print axioms IndependentETH.NonAffine.signedClause_exact
#print axioms IndependentETH.NonAffine.rawRows_equiv_rowHolds
#print axioms IndependentETH.NonAffine.checked_signed_cnf_exact
#print axioms IndependentETH.NonAffine.parityMask_exact
#print axioms IndependentETH.NonAffine.parityRows_exact
#print axioms IndependentETH.NonAffine.sourceRows_exact
#print axioms IndependentETH.NonAffine.checked_source_rows_exact
#print axioms IndependentETH.NonAffine.previous_next
#print axioms IndependentETH.NonAffine.next_previous
#print axioms IndependentETH.NonAffine.gadget_exact
#print axioms IndependentETH.NonAffine.orWindow_exact
#print axioms IndependentETH.NonAffine.accepted_iff_not_forbidden
#print axioms IndependentETH.NonAffine.count_eq_eight_sub_forbidden
#print axioms IndependentETH.NonAffine.homogeneous_count_seven

end IndependentETH.NonAffine
