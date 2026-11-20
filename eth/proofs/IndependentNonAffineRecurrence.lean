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


/-! ## Length-exact full assignments, without a seed-count shortcut

The following inductive relation describes *every bit* of a complete
satisfying word, rather than merely the three-bit starting state.
Its last constructor requires the final positive OR clause. Each step
writes the next complete-word bit and advances the recurrence state.
-/

def fullWord : State → List Bool → List Bool
  | (a, b, c), [] => [a, b, c]
  | (a, b, c), d :: ds => a :: fullWord (next d (a, b, c)) ds

theorem fullWord_length (s : State) (ds : List Bool) :
    (fullWord s ds).length = ds.length + 3 := by
  induction ds generalizing s with
  | nil =>
      rcases s with ⟨a, b, c⟩
      rfl
  | cons d ds ih =>
      rcases s with ⟨a, b, c⟩
      simp only [fullWord, List.length_cons]
      rw [ih]

inductive FullTrace : State → List Bool → List Bool → Prop
  | last (a b c : Bool) (h : nonzero (a, b, c) = true) :
      FullTrace (a, b, c) [] [a, b, c]
  | step (a b c d : Bool) (ds tail : List Bool)
      (h : nonzero (a, b, c) = true)
      (ht : FullTrace (next d (a, b, c)) ds tail) :
      FullTrace (a, b, c) (d :: ds) (a :: tail)

theorem fullTrace_word {s : State} {ds w : List Bool}
    (h : FullTrace s ds w) : w = fullWord s ds := by
  induction h with
  | last a b c h => rfl
  | step a b c d ds tail h ht ih => simpa [fullWord] using congrArg (List.cons a) ih

theorem fullTrace_length {s : State} {ds w : List Bool}
    (h : FullTrace s ds w) : w.length = ds.length + 3 := by
  rw [fullTrace_word h]
  exact fullWord_length s ds

theorem fullTrace_accepts {s : State} {ds w : List Bool}
    (h : FullTrace s ds w) : accepts s ds = true := by
  induction h with
  | last a b c h => exact h
  | step a b c d ds tail h ht ih =>
      change (nonzero (a, b, c) && accepts (next d (a, b, c)) ds) = true
      simp [h, ih]

theorem accepted_fullTrace (s : State) (ds : List Bool)
    (h : accepts s ds = true) : FullTrace s ds (fullWord s ds) := by
  induction ds generalizing s with
  | nil =>
      rcases s with ⟨a, b, c⟩
      exact FullTrace.last a b c h
  | cons d ds ih =>
      rcases s with ⟨a, b, c⟩
      have hp : nonzero (a, b, c) = true ∧
          accepts (next d (a, b, c)) ds = true := by
        cases h0 : nonzero (a, b, c) <;>
          cases h1 : accepts (next d (a, b, c)) ds <;>
          simp [accepts, h0, h1] at h ⊢
      obtain ⟨hs, ht⟩ := hp
      exact FullTrace.step a b c d ds
        (fullWord (next d (a, b, c)) ds) hs (ih _ ht)

/-- Complete, length-checked witnesses of the recurrence plus all positive
sliding-window clauses. This is *not* the type of arbitrary decoded CSR
bytes; the independent checked-source-row theorem handles that predicate. -/
def FullWitnesses (ds : List Bool) :=
  { p : State × List Bool // FullTrace p.1 ds p.2 }

def AcceptedSeeds (ds : List Bool) :=
  { s : State // accepts s ds = true }

/-- Every certified full word, including its exact length, is uniquely
determined by one accepted seed; conversely every accepted seed extends to
exactly one full word. No assignment over 2^n is enumerated. -/
def fullWitnessSeedEquiv (ds : List Bool) :
    FullWitnesses ds ≃ AcceptedSeeds ds where
  toFun p := ⟨p.1.1, fullTrace_accepts p.2⟩
  invFun s := ⟨(s.1, fullWord s.1 ds), accepted_fullTrace s.1 ds s.2⟩
  left_inv := by
    rintro ⟨⟨s, w⟩, h⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (fullTrace_word h).symm
  right_inv := by
    intro s
    apply Subtype.ext
    rfl


/-! ## Complete signed 3-CNF words, not merely recurrence traces

Each step imposes *the four actual ternary clauses* via parityGadget
and the current positive OR clause via orWindow. The final constructor
imposes the final OR clause. All bits, including each fourth bit e, are
explicitly supplied by the source word rather than computed in advance.
-/

theorem gadget_forces_next (d a b e : Bool) :
    parityGadget d a b e = true ↔
      e = Bool.xor (Bool.xor a b) d := by
  cases d <;> cases a <;> cases b <;> cases e <;> decide

inductive SourceCNFWord : State → List Bool → List Bool → Prop
  | last (a b c : Bool) (h : orWindow (a, b, c) = true) :
      SourceCNFWord (a, b, c) [] [a, b, c]
  | step (a b c d e : Bool) (ds tail : List Bool)
      (hOr : orWindow (a, b, c) = true)
      (hParity : parityGadget d a b e = true)
      (hTail : SourceCNFWord (b, c, e) ds tail) :
      SourceCNFWord (a, b, c) (d :: ds) (a :: tail)

theorem sourceCNFWord_to_trace {s : State} {ds w : List Bool}
    (h : SourceCNFWord s ds w) : FullTrace s ds w := by
  induction h with
  | last a b c h =>
      exact FullTrace.last a b c (by simpa only [orWindow_exact] using h)
  | step a b c d e ds tail hOr hParity hTail ih =>
      have he : e = Bool.xor (Bool.xor a b) d :=
        (gadget_forces_next d a b e).mp hParity
      subst e
      have hn : nonzero (a, b, c) = true := by
        simpa only [orWindow_exact] using hOr
      exact FullTrace.step a b c d ds tail hn ih

theorem fullTrace_to_sourceCNFWord {s : State} {ds w : List Bool}
    (h : FullTrace s ds w) : SourceCNFWord s ds w := by
  induction h with
  | last a b c h =>
      exact SourceCNFWord.last a b c (by simpa only [orWindow_exact] using h)
  | step a b c d ds tail h hTail ih =>
      have ho : orWindow (a, b, c) = true := by
        simpa only [orWindow_exact] using h
      have hp : parityGadget d a b (Bool.xor (Bool.xor a b) d) = true :=
        (gadget_forces_next d a b _).mpr rfl
      exact SourceCNFWord.step a b c d
        (Bool.xor (Bool.xor a b) d) ds tail ho hp ih

theorem sourceCNFWord_iff_trace (s : State) (ds w : List Bool) :
    SourceCNFWord s ds w ↔ FullTrace s ds w :=
  ⟨sourceCNFWord_to_trace, fullTrace_to_sourceCNFWord⟩

theorem sourceCNFWord_length {s : State} {ds w : List Bool}
    (h : SourceCNFWord s ds w) : w.length = ds.length + 3 :=
  fullTrace_length (sourceCNFWord_to_trace h)

/-- The source CNF's complete satisfying-word witnesses are a *different*
representation from the recurrence traces: their constructors test each
literal-gadget clause. The equivalence is proved from the local truth table. -/
def SourceWitnesses (ds : List Bool) :=
  { p : State × List Bool // SourceCNFWord p.1 ds p.2 }

def sourceWitnessTraceEquiv (ds : List Bool) :
    SourceWitnesses ds ≃ FullWitnesses ds where
  toFun p := ⟨p.1, sourceCNFWord_to_trace p.2⟩
  invFun p := ⟨p.1, fullTrace_to_sourceCNFWord p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    rfl
  right_inv := by
    intro p
    apply Subtype.ext
    rfl

/-- Exact finite-length SAT correspondence for all source-gadget CNF
witnesses: one and only one complete word for each accepted seed. -/
def sourceWitnessSeedEquiv (ds : List Bool) :
    SourceWitnesses ds ≃ AcceptedSeeds ds :=
  (sourceWitnessTraceEquiv ds).trans (fullWitnessSeedEquiv ds)


/-! ## Remove the redundant seed: actual full Boolean words

The prefix of any source word is the purported starting seed, so the
witness does not actually need to *store* the seed. This gives a
bijection whose source type contains only a satisfying Boolean word
with its checked full-length CNF predicate.
-/

def statePrefix : State → List Bool
  | (a, b, c) => [a, b, c]

theorem sourceCNFWord_prefix {s : State} {ds w : List Bool}
    (h : SourceCNFWord s ds w) :
    ∃ suffix : List Bool, w = statePrefix s ++ suffix := by
  induction h with
  | last a b c h =>
      exact ⟨[], rfl⟩
  | step a b c d e ds tail hOr hParity hTail ih =>
      obtain ⟨suffix, hw⟩ := ih
      refine ⟨e :: suffix, ?_⟩
      simp [statePrefix, hw]

/-- Extract the actual initial three bits, not a seed attached by a
certificate producer. Short or malformed words return zero, but cannot
satisfy the SourceCNFWord predicate. -/
def wordSeed : List Bool → State
  | a :: b :: c :: _ => (a, b, c)
  | _ => zeroState

theorem sourceCNFWord_seed {s : State} {ds w : List Bool}
    (h : SourceCNFWord s ds w) : wordSeed w = s := by
  obtain ⟨suffix, hw⟩ := sourceCNFWord_prefix h
  rcases s with ⟨a, b, c⟩
  simp [statePrefix, wordSeed, hw]

/-- The element is only the full length-exact word. Its proof is erased,
and there is no independently supplied or trusted starting seed. -/
def WordSolutions (ds : List Bool) :=
  { w : List Bool // ∃ s, SourceCNFWord s ds w }

theorem wordSolutions_length (ds : List Bool) (w : WordSolutions ds) :
    w.1.length = ds.length + 3 := by
  obtain ⟨s, hw⟩ := w.2
  exact sourceCNFWord_length hw

def wordSolutionsSeedEquiv (ds : List Bool) :
    WordSolutions ds ≃ AcceptedSeeds ds where
  toFun p := ⟨wordSeed p.1, by
    obtain ⟨s, hs⟩ := p.2
    rw [sourceCNFWord_seed hs]
    exact fullTrace_accepts (sourceCNFWord_to_trace hs)⟩
  invFun p := ⟨fullWord p.1 ds,
    ⟨p.1, fullTrace_to_sourceCNFWord
      (accepted_fullTrace p.1 ds p.2)⟩⟩
  left_inv := by
    rintro ⟨w, ⟨s, h⟩⟩
    apply Subtype.ext
    change fullWord (wordSeed w) ds = w
    rw [sourceCNFWord_seed h]
    exact (fullTrace_word (sourceCNFWord_to_trace h)).symm
  right_inv := by
    intro s
    apply Subtype.ext
    change wordSeed (fullWord s.1 ds) = s.1
    exact sourceCNFWord_seed
      (fullTrace_to_sourceCNFWord (accepted_fullTrace s.1 ds s.2))

/-! ## One-step composition along the three-variable boundary

Removing the first parity gadget and the first positive OR clause leaves
the same source problem on the shifted variable assignment. This theorem
is about the existing indexed signed-row semantics, not a replacement
definition of a new formula. -/

def shiftAssignment (x : Nat → Bool) : Nat → Bool := fun i => x (i + 1)

theorem sourceRows_step (d : Bool) (ds : List Bool) (x : Nat → Bool) :
    allRowsHold x (sourceRows (d :: ds)) ↔
      parityState (tripleAt x 0 1 3) = d ∧
      tripleAt x 0 1 2 ≠ zeroState ∧
      allRowsHold (shiftAssignment x) (sourceRows ds) := by
  rw [sourceRows_exact (d :: ds) x,
      sourceRows_exact ds (shiftAssignment x)]
  constructor
  · rintro ⟨hp, ho⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [tripleAt] using hp 0 (by simp)
    · simpa [tripleAt] using ho 0 (by simp)
    · intro i hi
      have h := hp (i + 1) (by simp; omega)
      simpa [shiftAssignment, tripleAt, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using h
    · intro i hi
      have h := ho (i + 1) (by simp; omega)
      simpa [shiftAssignment, tripleAt, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using h
  · rintro ⟨hpar, hor, hp, ho⟩
    constructor
    · intro i hi
      cases i with
      | zero =>
          simpa [tripleAt] using hpar
      | succ i =>
          have hi' : i < ds.length := by simp at hi; omega
          have h := hp i hi'
          simpa [shiftAssignment, tripleAt, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using h
    · intro i hi
      cases i with
      | zero =>
          simpa [tripleAt] using hor
      | succ i =>
          have hi' : i < ds.length + 1 := by simp at hi; omega
          have h := ho i hi'
          simpa [shiftAssignment, tripleAt, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using h

/-- Interpret an entire finite Boolean word as a total assignment, using
false outside its declared range. For any valid source witness, all checked
rows refer only to the word's declared variable domain. -/
def wordAssignment (w : List Bool) (i : Nat) : Bool :=
  (w[i]?).getD false

theorem wordAssignment_shift (a : Bool) (tail : List Bool) :
    shiftAssignment (wordAssignment (a :: tail)) = wordAssignment tail := by
  funext i
  rfl

/-- Every clause-level complete word really satisfies all of the indexed
signed incidence rows. This is a substantive direction of the list-to-row
semantics bridge, not merely a restatement of a definition. -/
theorem sourceCNFWord_rows {s : State} {ds w : List Bool}
    (h : SourceCNFWord s ds w) :
    allRowsHold (wordAssignment w) (sourceRows ds) := by
  induction h with
  | last a b c h =>
      apply (sourceRows_exact [] (wordAssignment [a, b, c])).2
      constructor
      · intro i hi
        simp at hi
      · intro i hi
        have hi0 : i = 0 := by
          simp at hi
          omega
        subst i
        have hn : nonzero (a, b, c) = true := by
          simpa only [orWindow_exact] using h
        have hz : (a, b, c) ≠ zeroState := of_decide_eq_true hn
        simpa [tripleAt, wordAssignment] using hz
  | step a b c d e ds tail hOr hParity hTail ih =>
      apply (sourceRows_step d ds (wordAssignment (a :: tail))).2
      obtain ⟨suffix, hpref⟩ := sourceCNFWord_prefix hTail
      have hwindow : tripleAt (wordAssignment (a :: tail)) 0 1 2 = (a, b, c) := by
        simp [tripleAt, wordAssignment, hpref, statePrefix]
      have hparity : tripleAt (wordAssignment (a :: tail)) 0 1 3 = (a, b, e) := by
        simp [tripleAt, wordAssignment, hpref, statePrefix]
      have hp : parityState (a, b, e) = d := by
        rw [gadget_exact] at hParity
        exact of_decide_eq_true hParity
      have hn : nonzero (a, b, c) = true := by
        simpa only [orWindow_exact] using hOr
      have hz : (a, b, c) ≠ zeroState := of_decide_eq_true hn
      refine ⟨?_, ?_, ?_⟩
      · rw [hparity]
        exact hp
      · rw [hwindow]
        exact hz
      · rw [wordAssignment_shift]
        exact ih

#print axioms IndependentETH.NonAffine.wordAssignment_shift
#print axioms IndependentETH.NonAffine.sourceCNFWord_rows

#print axioms IndependentETH.NonAffine.sourceRows_step

/-! ## Checked signed CSR input and proof-producing receipt semantics

This is an executable Lean reference decoder for Rust-shaped offsets,
zero-based column indices, and signed polarities. Every row uses checked
indices, demands exactly three sorted distinct columns, and signs in {-1,+1}.
The complete decoder checks declared shape and absence of duplicate rows.
It returns none on malformed input rather than inventing a formula.

Natural-number offsets and integer signs model the mathematical values of
Rust usize and i8; this is NOT a machine-integer refinement theorem.
-/

structure SignedCsrInput where
  variableCount : Nat
  offsets : List Nat
  columns : List Nat
  signs : List Int
deriving Repr, DecidableEq

def polarityFromSign (z : Int) : Option Bool :=
  if z = -1 then some true
  else if z = 1 then some false
  else none

def decodeCsrRow (csr : SignedCsrInput) (i : Nat) : Option SignedRow := do
  let start ← csr.offsets[i]?
  let stop ← csr.offsets[i + 1]?
  if stop ≠ start + 3 then none
  else
    let a ← csr.columns[start]?
    let b ← csr.columns[start + 1]?
    let c ← csr.columns[start + 2]?
    let sa ← csr.signs[start]?
    let sb ← csr.signs[start + 1]?
    let sc ← csr.signs[start + 2]?
    let pa ← polarityFromSign sa
    let pb ← polarityFromSign sb
    let pc ← polarityFromSign sc
    if a < b ∧ b < c ∧ c < csr.variableCount then
      pure (row a b c (pa, pb, pc))
    else none

/-- Decode the complete row multiset, refusing shape mismatches, malformed
rows, and duplicates before converting it to a finite set. No row is dropped. -/
def decodeSignedCsr (csr : SignedCsrInput) : Option (Finset SignedRow) := do
  if csr.variableCount < 4 then none
  else
    let rowsCount := 5 * csr.variableCount - 14
    if csr.offsets.length = rowsCount + 1 ∧
        csr.columns.length = csr.signs.length ∧
        csr.offsets.head? = some 0 ∧
        csr.offsets[rowsCount]? = some csr.columns.length then
      let rows ← (List.range rowsCount).mapM (decodeCsrRow csr)
      if rows.Nodup then
        pure rows.toFinset
      else none
    else none

/-- The entire decoded CSR must match the canonical row set for the claimed
recurrence RHS, and every forbidden seed must match the independently
defined Boolean recurrence specification. -/
def checkCsrReceipt (csr : SignedCsrInput)
    (ds : List Bool) (mask : Finset State) : Bool :=
  decide (csr.variableCount = ds.length + 3 ∧
    decodeSignedCsr csr = some (sourceRows ds) ∧
    mask = forbidden ds)

theorem checkCsrReceipt_fields
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (h : checkCsrReceipt csr ds mask = true) :
    csr.variableCount = ds.length + 3 ∧
    decodeSignedCsr csr = some (sourceRows ds) ∧
    mask = forbidden ds := by
  exact of_decide_eq_true h

/-- Acceptance of a checked signed CSR certificate entails exact
signed-literal equivalence for every total source assignment. -/
theorem checkedCsr_allAssignments
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (h : checkCsrReceipt csr ds mask = true) :
    ∃ rows, decodeSignedCsr csr = some rows ∧
      ∀ x : Nat → Bool,
      (∀ r ∈ rows,
        signedClauseEval (tripleAt x r.first r.second r.third)
          r.falsifiesAt = true) ↔
      (∀ i, i < ds.length →
        parityState (tripleAt x i (i + 1) (i + 3)) = ds[i]!) ∧
      (∀ i, i < ds.length + 1 →
        tripleAt x i (i + 1) (i + 2) ≠ zeroState) := by
  have hc := checkCsrReceipt_fields csr ds mask h
  refine ⟨sourceRows ds, hc.2.1, ?_⟩
  intro x
  have hs : checkSourceRows (sourceRows ds) ds = true := by
    simp [checkSourceRows]
  exact checked_signed_cnf_exact (sourceRows ds) ds x hs

/-- The semantic count of this accepted certificate is the number of
complete satisfying Boolean words, not just a trace count. -/
theorem wordSolutions_card (ds : List Bool) :
    Nat.card (WordSolutions ds) = (accepted ds).card := by
  classical
  calc
    Nat.card (WordSolutions ds) =
        Nat.card (AcceptedSeeds ds) :=
      Nat.card_congr (wordSolutionsSeedEquiv ds)
    _ = (accepted ds).card := by
      simp [AcceptedSeeds, accepted, Nat.card_eq_fintype_card,
        Fintype.card_subtype]

theorem acceptedCsr_count_correct
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (h : checkCsrReceipt csr ds mask = true) :
    Nat.card (WordSolutions ds) = 8 - mask.card := by
  have hm : mask = forbidden ds := (checkCsrReceipt_fields csr ds mask h).2.2
  rw [hm, wordSolutions_card, count_eq_eight_sub_forbidden]

/-- Optional verifier result: malformed and unsupported CSR sources return
none. This is a proved Lean specification, not a claim that the separately
compiled Rust program is formally refined to it. -/
def verifyCsrCount (csr : SignedCsrInput)
    (ds : List Bool) (mask : Finset State) : Option Nat :=
  if checkCsrReceipt csr ds mask = true then some (8 - mask.card) else none

theorem verifyCsrCount_sound
    (csr : SignedCsrInput) (ds : List Bool)
    (mask : Finset State) (out : Nat)
    (h : verifyCsrCount csr ds mask = some out) :
    Nat.card (WordSolutions ds) = out := by
  unfold verifyCsrCount at h
  split at h
  · rename_i hc
    have hcount := acceptedCsr_count_correct csr ds mask hc
    cases h
    exact hcount
  · simp at h

/-! ## Fixed cross-language CSR test vector

These arrays are the concrete signed CSR rows for n=4, homogeneous RHS.
They match the Rust source fixture's signed-row convention. Unlike a
symbolic proof, these tests execute the checked decoder over literal input
and demonstrate exact acceptance, corruption refusal, and output seven.
-/

def smallHomogeneousCsr : SignedCsrInput where
  variableCount := 4
  offsets := [0, 3, 6, 9, 12, 15, 18]
  columns := [0, 1, 3, 0, 1, 3, 0, 1, 3, 0, 1, 2, 0, 1, 3, 1, 2, 3]
  signs := [-1, -1, -1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1]

def smallForbiddenMask : Finset State := {zeroState}

example : verifyCsrCount smallHomogeneousCsr [false] smallForbiddenMask = some 7 := by
  decide

example : verifyCsrCount
    { smallHomogeneousCsr with signs := [0] ++ smallHomogeneousCsr.signs.drop 1 }
    [false] smallForbiddenMask = none := by
  decide

example : verifyCsrCount
    { smallHomogeneousCsr with offsets := [0, 4, 6, 9, 12, 15, 18] }
    [false] smallForbiddenMask = none := by
  decide

#print axioms IndependentETH.NonAffine.checkCsrReceipt_fields
#print axioms IndependentETH.NonAffine.checkedCsr_allAssignments
#print axioms IndependentETH.NonAffine.wordSolutions_card
#print axioms IndependentETH.NonAffine.acceptedCsr_count_correct
#print axioms IndependentETH.NonAffine.verifyCsrCount_sound

#print axioms IndependentETH.NonAffine.sourceCNFWord_prefix
#print axioms IndependentETH.NonAffine.sourceCNFWord_seed
#print axioms IndependentETH.NonAffine.wordSolutions_length
#print axioms IndependentETH.NonAffine.wordSolutionsSeedEquiv

#print axioms IndependentETH.NonAffine.gadget_forces_next
#print axioms IndependentETH.NonAffine.sourceCNFWord_to_trace
#print axioms IndependentETH.NonAffine.fullTrace_to_sourceCNFWord
#print axioms IndependentETH.NonAffine.sourceCNFWord_iff_trace
#print axioms IndependentETH.NonAffine.sourceCNFWord_length
#print axioms IndependentETH.NonAffine.sourceWitnessSeedEquiv

#print axioms IndependentETH.NonAffine.fullWord_length
#print axioms IndependentETH.NonAffine.fullTrace_word
#print axioms IndependentETH.NonAffine.fullTrace_length
#print axioms IndependentETH.NonAffine.fullTrace_accepts
#print axioms IndependentETH.NonAffine.accepted_fullTrace
#print axioms IndependentETH.NonAffine.fullWitnessSeedEquiv

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
