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

/-- Every length-exact Boolean word satisfying *all* indexed signed rows
also admits a source-gadget CNF derivation. The proof recursively peels the
leading parity gadget and positive OR row using sourceRows_step; it does not
assume that the word originated from the recurrence constructor. -/
theorem indexedRows_sourceCNFWord (ds w : List Bool)
    (hlen : w.length = ds.length + 3)
    (hrows : allRowsHold (wordAssignment w) (sourceRows ds)) :
    ∃ s, SourceCNFWord s ds w := by
  induction ds generalizing w with
  | nil =>
      cases w with
      | nil => simp at hlen
      | cons a t1 =>
          cases t1 with
          | nil => simp at hlen
          | cons b t2 =>
              cases t2 with
              | nil => simp at hlen
              | cons c t3 =>
                  cases t3 with
                  | cons e rest => simp at hlen
                  | nil =>
                      have hdecoded :=
                        (sourceRows_exact [] (wordAssignment [a, b, c])).mp hrows
                      have hz : (a, b, c) ≠ zeroState := by
                        have h0 := hdecoded.2 0 (by simp)
                        simpa [tripleAt, wordAssignment] using h0
                      have hn : nonzero (a, b, c) = true := by
                        simp [nonzero, hz]
                      have ho : orWindow (a, b, c) = true := by
                        simpa only [orWindow_exact] using hn
                      exact ⟨(a, b, c), SourceCNFWord.last a b c ho⟩
  | cons d ds ih =>
      cases w with
      | nil => simp at hlen
      | cons a t1 =>
          cases t1 with
          | nil => simp at hlen
          | cons b t2 =>
              cases t2 with
              | nil => simp at hlen
              | cons c t3 =>
                  cases t3 with
                  | nil => simp at hlen
                  | cons e rest =>
                      have htailLength :
                          (b :: c :: e :: rest).length = ds.length + 3 := by
                        simp at hlen ⊢
                        omega
                      have hsplit :=
                        (sourceRows_step d ds
                          (wordAssignment (a :: b :: c :: e :: rest))).mp hrows
                      have hp : parityState (a, b, e) = d := by
                        simpa [wordAssignment, tripleAt] using hsplit.1
                      have hz : (a, b, c) ≠ zeroState := by
                        simpa [wordAssignment, tripleAt] using hsplit.2.1
                      have htailRows :
                          allRowsHold (wordAssignment (b :: c :: e :: rest))
                            (sourceRows ds) := by
                        simpa only [wordAssignment_shift] using hsplit.2.2
                      obtain ⟨s, hs⟩ := ih (b :: c :: e :: rest) htailLength htailRows
                      have hseed : s = (b, c, e) := by
                        simpa [wordSeed] using (sourceCNFWord_seed hs).symm
                      subst s
                      have hn : nonzero (a, b, c) = true := by
                        simp [nonzero, hz]
                      have ho : orWindow (a, b, c) = true := by
                        simpa only [orWindow_exact] using hn
                      have hg : parityGadget d a b e = true := by
                        rw [gadget_exact]
                        have hx : Bool.xor (Bool.xor a b) e = d := hp
                        simp [hx]
                      exact ⟨(a, b, c),
                        SourceCNFWord.step a b c d e ds (b :: c :: e :: rest)
                          ho hg hs⟩

/-- The exact indexed signed-row semantics and the independent
clause-by-clause full-word semantics coincide at every complete word. -/
theorem sourceCNFWord_iff_indexedRows (ds w : List Bool) :
    (∃ s, SourceCNFWord s ds w) ↔
      w.length = ds.length + 3 ∧
      allRowsHold (wordAssignment w) (sourceRows ds) := by
  constructor
  · rintro ⟨s, h⟩
    exact ⟨sourceCNFWord_length h, sourceCNFWord_rows h⟩
  · rintro ⟨hlen, hrows⟩
    exact indexedRows_sourceCNFWord ds w hlen hrows

def IndexedRowWords (ds : List Bool) :=
  { w : List Bool // w.length = ds.length + 3 ∧
    allRowsHold (wordAssignment w) (sourceRows ds) }

def indexedRowWordsEquiv (ds : List Bool) :
    IndexedRowWords ds ≃ WordSolutions ds where
  toFun w := ⟨w.1, (sourceCNFWord_iff_indexedRows ds w.1).mpr w.2⟩
  invFun w := ⟨w.1, (sourceCNFWord_iff_indexedRows ds w.1).mp w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

#print axioms IndependentETH.NonAffine.indexedRows_sourceCNFWord
#print axioms IndependentETH.NonAffine.sourceCNFWord_iff_indexedRows
#print axioms IndependentETH.NonAffine.indexedRowWordsEquiv

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

/-- This is the final mathematical counting statement for all length-exact
words satisfying the *decoded indexed signed rows*, not a separate
seed-only or trace-only surrogate. -/
theorem verifiedCsr_indexedWordCount
    (csr : SignedCsrInput) (ds : List Bool)
    (mask : Finset State) (out : Nat)
    (h : verifyCsrCount csr ds mask = some out) :
    Nat.card (IndexedRowWords ds) = out := by
  rw [Nat.card_congr (indexedRowWordsEquiv ds)]
  exact verifyCsrCount_sound csr ds mask out h

/-! ## Final decoded-CSR word semantics

The counted objects below are *only* finite Boolean words. Their predicate
evaluates the actual rows produced by the checked CSR decoder, rather than
silently substituting the expected canonical source rows. -/

def DecodedCsrWords (csr : SignedCsrInput) (ds : List Bool) :=
  { w : List Bool // w.length = ds.length + 3 ∧
    ∃ rows : Finset SignedRow,
      decodeSignedCsr csr = some rows ∧
      allRowsHold (wordAssignment w) rows }

theorem verifyCsrCount_implies_check
    (csr : SignedCsrInput) (ds : List Bool)
    (mask : Finset State) (out : Nat)
    (h : verifyCsrCount csr ds mask = some out) :
    checkCsrReceipt csr ds mask = true := by
  unfold verifyCsrCount at h
  split at h
  · assumption
  · simp at h

theorem decodedCsrWords_condition
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (hcheck : checkCsrReceipt csr ds mask = true) (w : List Bool) :
    (w.length = ds.length + 3 ∧
      ∃ rows : Finset SignedRow,
        decodeSignedCsr csr = some rows ∧
        allRowsHold (wordAssignment w) rows) ↔
    (w.length = ds.length + 3 ∧
      allRowsHold (wordAssignment w) (sourceRows ds)) := by
  have hd : decodeSignedCsr csr = some (sourceRows ds) :=
    (checkCsrReceipt_fields csr ds mask hcheck).2.1
  constructor
  · rintro ⟨hlen, rows, hdecoded, hholds⟩
    have heq : rows = sourceRows ds :=
      Option.some.inj (hdecoded.symm.trans hd)
    subst rows
    exact ⟨hlen, hholds⟩
  · rintro ⟨hlen, hholds⟩
    exact ⟨hlen, sourceRows ds, hd, hholds⟩

def decodedCsrWordsEquiv
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (hcheck : checkCsrReceipt csr ds mask = true) :
    DecodedCsrWords csr ds ≃ IndexedRowWords ds where
  toFun w := ⟨w.1, (decodedCsrWords_condition csr ds mask hcheck w.1).mp w.2⟩
  invFun w := ⟨w.1, (decodedCsrWords_condition csr ds mask hcheck w.1).mpr w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

/-- A successful executable Lean CSR verification returns exactly the
number of finite Boolean words satisfying all of the *decoded input rows*.
No untrusted reconstructed RHS or mask is assumed correct. -/
theorem verifiedCsr_decodedWordCount
    (csr : SignedCsrInput) (ds : List Bool)
    (mask : Finset State) (out : Nat)
    (h : verifyCsrCount csr ds mask = some out) :
    Nat.card (DecodedCsrWords csr ds) = out := by
  have hc := verifyCsrCount_implies_check csr ds mask out h
  rw [Nat.card_congr (decodedCsrWordsEquiv csr ds mask hc)]
  exact verifiedCsr_indexedWordCount csr ds mask out h

#print axioms IndependentETH.NonAffine.verifyCsrCount_implies_check
#print axioms IndependentETH.NonAffine.decodedCsrWords_condition
#print axioms IndependentETH.NonAffine.decodedCsrWordsEquiv
#print axioms IndependentETH.NonAffine.verifiedCsr_decodedWordCount

#print axioms IndependentETH.NonAffine.verifiedCsr_indexedWordCount

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

/-! ## Rust-shaped single-row representation refinement

The independently ordered local Rust model checks columns before signs;
the executable Lean decoder reads signs first. This proves equality of both
success and refusal on a witnessed three-literal CSR slice. Machine-word
bounds are explicit, but physical Rust execution and allocations remain open.
-/

/-- Model the Rust sign test, checking positive polarity first.
The existing Lean specification checks negative polarity first. -/
def rustLiteralBit (z : Int) : Option Bool :=
  if z = 1 then some false
  else if z = -1 then some true
  else none

theorem rustLiteralBit_eq_polarityFromSign (z : Int) :
    rustLiteralBit z = polarityFromSign z := by
  by_cases hp : z = 1
  · have hn : z ≠ -1 := by omega
    simp [rustLiteralBit, polarityFromSign, hp]
  · by_cases hn : z = -1
    · simp [rustLiteralBit, polarityFromSign, hn]
    · simp [rustLiteralBit, polarityFromSign, hp, hn]

/-- A separate semantic model of one Rust-recognized three-literal slice.
It checks strict, in-range columns before decoding the three signed i8
polarity values, as the production Rust recognizer does. -/
def rustTripleRow (n a b c : Nat) (sa sb sc : Int) : Option SignedRow :=
  if a < b ∧ b < c ∧ c < n then do
    let pa ← rustLiteralBit sa
    let pb ← rustLiteralBit sb
    let pc ← rustLiteralBit sc
    pure (row a b c (pa, pb, pc))
  else none

/-- Rust's checked subtraction criterion and Lean's addition criterion
describe exactly the same row width when the offsets are ordered. -/
theorem rustWidth_iff_leanWidth (start stop : Nat) (h : start ≤ stop) :
    stop - start = 3 ↔ stop = start + 3 := by
  omega

/-- The complete one-row refinement. All source observations are stated
explicitly: two offsets, all three columns, and all three signs. The
subtraction-based slice check entails the equality required by the
existing Lean decoder. No sign or column can be silently dropped.

This proves BOTH acceptance and refusal equality for the witnessed row,
including bad signs, duplicate/out-of-range columns, and wrong column
order. Malformed offsets are treated by the separate refusal theorem.
-/
theorem rustTripleRow_eq_decodeCsrRow
    (csr : SignedCsrInput) (i start stop a b c : Nat)
    (sa sb sc : Int)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hshape : start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3)
    (ha : csr.columns[start]? = some a)
    (hb : csr.columns[start + 1]? = some b)
    (hc : csr.columns[start + 2]? = some c)
    (hsa : csr.signs[start]? = some sa)
    (hsb : csr.signs[start + 1]? = some sb)
    (hsc : csr.signs[start + 2]? = some sc) :
    rustTripleRow csr.variableCount a b c sa sb sc = decodeCsrRow csr i := by
  have hwidth : stop = start + 3 :=
    (rustWidth_iff_leanWidth start stop hshape.1).mp hshape.2.2
  cases hpa : polarityFromSign sa with
  | none =>
      simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
        hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa]
  | some pa =>
      cases hpb : polarityFromSign sb with
      | none =>
          simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
            hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa, hpb]
      | some pb =>
          cases hpc : polarityFromSign sc with
          | none =>
              simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
                hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa, hpb, hpc]
          | some pc =>
              simp [rustTripleRow, decodeCsrRow, rustLiteralBit_eq_polarityFromSign,
                hstart, hstop, hwidth, ha, hb, hc, hsa, hsb, hsc, hpa, hpb, hpc]

/-- Under the same witnessed, in-bounds row, all refusals agree, not only
successful outputs. A forbidden sign, unsorted or duplicated columns, or
an out-of-range column is rejected on both sides. -/
theorem rustTripleRow_refusal_iff
    (csr : SignedCsrInput) (i start stop a b c : Nat)
    (sa sb sc : Int)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hshape : start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3)
    (ha : csr.columns[start]? = some a)
    (hb : csr.columns[start + 1]? = some b)
    (hc : csr.columns[start + 2]? = some c)
    (hsa : csr.signs[start]? = some sa)
    (hsb : csr.signs[start + 1]? = some sb)
    (hsc : csr.signs[start + 2]? = some sc) :
    (rustTripleRow csr.variableCount a b c sa sb sc = none) ↔
      (decodeCsrRow csr i = none) := by
  rw [rustTripleRow_eq_decodeCsrRow csr i start stop a b c sa sb sc
    hstart hstop hshape ha hb hc hsa hsb hsc]

/-- A malformed local width is always refused by the original Lean decoder.
The preceding width theorem identifies the corresponding Rust subtraction
failure whenever the start and stop offsets are ordered. -/
theorem decodeCsrRow_badWidth
    (csr : SignedCsrInput) (i start stop : Nat)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hbad : stop ≠ start + 3) :
    decodeCsrRow csr i = none := by
  simp [decodeCsrRow, hstart, hstop, hbad]

/-- The supported machine boundary is explicit rather than silently
identifying arbitrarily large Lean natural numbers with Rust usize. -/
def rustRowMachineBounds (wordBits : Nat) (csr : SignedCsrInput)
    (start stop : Nat) (sa sb sc : Int) : Prop :=
  csr.variableCount < 2 ^ wordBits ∧
  csr.columns.length < 2 ^ wordBits ∧
  csr.signs.length = csr.columns.length ∧
  csr.offsets.length < 2 ^ wordBits ∧
  (∀ col ∈ csr.columns, col < 2 ^ wordBits) ∧
  (∀ offset ∈ csr.offsets, offset < 2 ^ wordBits) ∧
  (∀ sign ∈ csr.signs, -128 ≤ sign ∧ sign ≤ 127) ∧
  start < 2 ^ wordBits ∧ stop < 2 ^ wordBits ∧
  (-128 ≤ sa ∧ sa ≤ 127) ∧
  (-128 ≤ sb ∧ sb ≤ 127) ∧
  (-128 ≤ sc ∧ sc ≤ 127)

/-- Explicitly bounded specialization: if the Rust arrays can be represented
and the checked row witnesses are the ones read from those arrays, the
semantic decoders agree. The boundedness assumption here is about data
representation, not Rust execution or memory allocation. -/
theorem rustTripleRow_bounded_refinement
    (wordBits : Nat) (csr : SignedCsrInput) (i start stop a b c : Nat)
    (sa sb sc : Int)
    (_hMachine : rustRowMachineBounds wordBits csr start stop sa sb sc)
    (hstart : csr.offsets[i]? = some start)
    (hstop : csr.offsets[i + 1]? = some stop)
    (hshape : start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3)
    (ha : csr.columns[start]? = some a)
    (hb : csr.columns[start + 1]? = some b)
    (hc : csr.columns[start + 2]? = some c)
    (hsa : csr.signs[start]? = some sa)
    (hsb : csr.signs[start + 1]? = some sb)
    (hsc : csr.signs[start + 2]? = some sc) :
    rustTripleRow csr.variableCount a b c sa sb sc = decodeCsrRow csr i :=
  rustTripleRow_eq_decodeCsrRow csr i start stop a b c sa sb sc
    hstart hstop hshape ha hb hc hsa hsb hsc

#print axioms IndependentETH.NonAffine.rustLiteralBit_eq_polarityFromSign
#print axioms IndependentETH.NonAffine.rustWidth_iff_leanWidth
#print axioms IndependentETH.NonAffine.rustTripleRow_eq_decodeCsrRow
#print axioms IndependentETH.NonAffine.rustTripleRow_refusal_iff
#print axioms IndependentETH.NonAffine.decodeCsrRow_badWidth
#print axioms IndependentETH.NonAffine.rustTripleRow_bounded_refinement

/-! ## Whole-CSR semantic composition

A Rust-shaped scanner validates offsets with subtraction and reads array
elements before applying the signed three-column row check. Its outer
structure checks the declared CSR shape and rejects duplicate decoded rows
before constructing a finite set. This is a *pure semantic model* of the
validation boundary, not a refinement of BTreeMap allocation or machine code.
-/

/-- Rust-style offset and array observations for one row. The shape guard
corresponds to the negation of the Rust malformed-offset refusal test.
The remaining decoder uses the previously refined Rust-shaped row predicate.
No array access is unchecked in this model. -/
def rustScanCsrRow (csr : SignedCsrInput) (i : Nat) : Option SignedRow := do
  let start ← csr.offsets[i]?
  let stop ← csr.offsets[i + 1]?
  if start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3 then
    let a ← csr.columns[start]?
    let b ← csr.columns[start + 1]?
    let c ← csr.columns[start + 2]?
    let sa ← csr.signs[start]?
    let sb ← csr.signs[start + 1]?
    let sc ← csr.signs[start + 2]?
    rustTripleRow csr.variableCount a b c sa sb sc
  else none

/-- The three sign bits as a Rust-compatible integer polarity, with the
least significant bit corresponding to the first column. -/
def rustPolarityIndex : State → Nat
  | (p, q, r) =>
      (if p then 1 else 0) + (if q then 2 else 0) + (if r then 4 else 0)

/-- Each of the eight polarity values has a unique three-bit encoding. -/
theorem rustPolarityIndex_injective : Function.Injective rustPolarityIndex := by
  intro p q h
  rcases p with ⟨a, b, c⟩
  rcases q with ⟨d, e, f⟩
  cases a <;> cases b <;> cases c <;>
    cases d <;> cases e <;> cases f <;>
    simp [rustPolarityIndex] at h ⊢

/-- Semantic key used by Rust's column-triple to polarity-mask grouping.
The implementation uses a three-usize key and an eight-bit bitset; comparing
one key/polarity pair is equivalent to comparing this value. -/
def rustGroupingKey (r : SignedRow) : Nat × Nat × Nat × Nat :=
  (r.first, r.second, r.third, rustPolarityIndex r.falsifiesAt)

theorem rustGroupingKey_injective : Function.Injective rustGroupingKey := by
  intro r s h
  cases r with
  | mk i j k p =>
      cases s with
      | mk i' j' k' p' =>
          simp only [rustGroupingKey, Prod.mk.injEq] at h
          rcases h with ⟨hi, hj, hk, hp⟩
          subst i'
          subst j'
          subst k'
          have heq : p = p' := rustPolarityIndex_injective hp
          subst p'
          rfl

/-- A Rust-style duplicate keyed by columns and the three-bit polarity
is exactly a duplicate full SignedRow. Distinct polarity clauses on the
same triple remain distinct, as required by a four-clause parity gadget. -/
theorem rustGroupingKey_nodup_iff (rows : List SignedRow) :
    (rows.map rustGroupingKey).Nodup ↔ rows.Nodup := by
  constructor
  · intro h
    exact List.Pairwise.of_map rustGroupingKey
      (fun a b hne heq => hne (congrArg rustGroupingKey heq)) h
  · intro h
    exact List.Pairwise.map rustGroupingKey
      (fun a b hne heq => hne (rustGroupingKey_injective heq)) h

/-- The entire *mathematical* CSR collection, with all row scans and duplicate
checks. The Rust recognizer's later gadget grouping and receipt logic are not
represented by this function. Arithmetic overflow is outside this definition
and belongs to its explicitly bounded refinement domain. -/
def rustScanSignedCsr (csr : SignedCsrInput) : Option (Finset SignedRow) := do
  if csr.variableCount < 4 then none
  else
    let rowsCount := 5 * csr.variableCount - 14
    if csr.offsets.length = rowsCount + 1 ∧
        csr.columns.length = csr.signs.length ∧
        csr.offsets.head? = some 0 ∧
        csr.offsets[rowsCount]? = some csr.columns.length then
      let rows ← (List.range rowsCount).mapM (rustScanCsrRow csr)
      if (rows.map rustGroupingKey).Nodup then
        pure rows.toFinset
      else none
    else none

/-- All six observed row entries are explicit. This is the stable
representation contract for transferring the previous local proof to
an arbitrary row index; no value is guessed from a canonical fixture. -/
def HasRustRowSlice (csr : SignedCsrInput) (i : Nat) : Prop :=
  ∃ (start stop a b c : Nat) (sa sb sc : Int),
    csr.offsets[i]? = some start ∧
    csr.offsets[i + 1]? = some stop ∧
    (start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3) ∧
    csr.columns[start]? = some a ∧
    csr.columns[start + 1]? = some b ∧
    csr.columns[start + 2]? = some c ∧
    csr.signs[start]? = some sa ∧
    csr.signs[start + 1]? = some sb ∧
    csr.signs[start + 2]? = some sc

/-- A witnessed row scan refines the existing executable Lean decoder.
This is an equality of Option values, so it includes all semantic refusals
from malformed columns or polarities, not just successful rows. -/
theorem rustScanCsrRow_eq_decodeCsrRow
    (csr : SignedCsrInput) (i : Nat) (h : HasRustRowSlice csr i) :
    rustScanCsrRow csr i = decodeCsrRow csr i := by
  rcases h with ⟨start, stop, a, b, c, sa, sb, sc,
    hstart, hstop, hshape, ha, hb, hc, hsa, hsb, hsc⟩
  have hscan : rustScanCsrRow csr i =
      rustTripleRow csr.variableCount a b c sa sb sc := by
    simp [rustScanCsrRow, hstart, hstop, hshape, ha, hb, hc, hsa, hsb, hsc]
  calc
    rustScanCsrRow csr i =
        rustTripleRow csr.variableCount a b c sa sb sc := hscan
    _ = decodeCsrRow csr i :=
      rustTripleRow_eq_decodeCsrRow csr i start stop a b c sa sb sc
        hstart hstop hshape ha hb hc hsa hsb hsc

/-- All malformed-offset cases are covered, without a valid-slice witness.
If an index or offset is missing, both decoders refuse. If the mathematical
width differs from three, neither decoder can accept. When width is three
but the last offset exceeds the column array, the third checked Lean column
lookup fails. Remaining in-range cases agree on values and polarity. -/
theorem rustScanCsrRow_total_refinement (csr : SignedCsrInput) (i : Nat) :
    rustScanCsrRow csr i = decodeCsrRow csr i := by
  cases hs : csr.offsets[i]? with
  | none => simp [rustScanCsrRow, decodeCsrRow, hs]
  | some start =>
    cases he : csr.offsets[i + 1]? with
    | none => simp [rustScanCsrRow, decodeCsrRow, hs, he]
    | some stop =>
      by_cases hw : stop = start + 3
      · by_cases hb : stop ≤ csr.columns.length
        · have hb' : start + 3 ≤ csr.columns.length := by omega
          cases ha : csr.columns[start]? with
          | none =>
              have hmissing := (List.getElem?_eq_none_iff).mp ha
              omega
          | some a =>
            cases hbb : csr.columns[start + 1]? with
            | none =>
                have hmissing := (List.getElem?_eq_none_iff).mp hbb
                omega
            | some b =>
              cases hc : csr.columns[start + 2]? with
              | none =>
                  have hmissing := (List.getElem?_eq_none_iff).mp hc
                  omega
              | some c =>
                by_cases hsorted : a < b ∧ b < c ∧ c < csr.variableCount
                · simp [rustScanCsrRow, decodeCsrRow, hs, he,
                    hw, hb', ha, hbb, hc, rustTripleRow,
                    rustLiteralBit_eq_polarityFromSign, hsorted]
                · simp [rustScanCsrRow, decodeCsrRow, hs, he,
                    hw, hb', ha, hbb, hc, rustTripleRow,
                    rustLiteralBit_eq_polarityFromSign, hsorted]
        · have hmissing : csr.columns[start + 2]? = none := by
            apply List.getElem?_eq_none
            omega
          simp [rustScanCsrRow, decodeCsrRow, hs, he, hw, hmissing]
      · have hbad : ¬(start ≤ stop ∧
            stop ≤ csr.columns.length ∧ stop - start = 3) := by omega
        simp [rustScanCsrRow, decodeCsrRow, hs, he, hw, hbad]

/-- Pointwise Option equality composes through arbitrary sequential row
traversal, including early refusal. This establishes the first genuine
list-level bridge, independently of row ordering. -/
theorem csrRowMapM_congr (csr : SignedCsrInput) (indices : List Nat)
    (h : ∀ i ∈ indices, rustScanCsrRow csr i = decodeCsrRow csr i) :
    indices.mapM (rustScanCsrRow csr) =
      indices.mapM (decodeCsrRow csr) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      have hi : rustScanCsrRow csr i = decodeCsrRow csr i :=
        h i (by simp)
      have ht : ∀ j ∈ rest, rustScanCsrRow csr j = decodeCsrRow csr j := by
        intro j hj
        exact h j (by simp [hj])
      simp [List.mapM_cons, hi, ih ht]

/-- Under a row-wise agreement hypothesis, whole-CSR scanning and duplicate
rejection produce exactly the same finite row set, or both refuse. The
hypothesis can be discharged by the local row-witness theorem, rather than
assuming equality of the final clause sets. -/
theorem rustScanSignedCsr_eq_decodeSignedCsr_of_row_agreement
    (csr : SignedCsrInput)
    (h : ∀ i ∈ List.range (5 * csr.variableCount - 14),
      rustScanCsrRow csr i = decodeCsrRow csr i) :
    rustScanSignedCsr csr = decodeSignedCsr csr := by
  have hmap := csrRowMapM_congr csr
    (List.range (5 * csr.variableCount - 14)) h
  simp [rustScanSignedCsr, decodeSignedCsr, hmap,
    rustGroupingKey_nodup_iff]

/-- An arbitrary collection of witnessed rows, not merely the n=4 fixture,
satisfies the full-set representation refinement. Duplicate rows are
refused by both scanners, as are malformed signs/columns inside witnesses. -/
theorem rustScanSignedCsr_eq_decodeSignedCsr
    (csr : SignedCsrInput)
    (h : ∀ i ∈ List.range (5 * csr.variableCount - 14),
      HasRustRowSlice csr i) :
    rustScanSignedCsr csr = decodeSignedCsr csr := by
  apply rustScanSignedCsr_eq_decodeSignedCsr_of_row_agreement
  intro i hi
  exact rustScanCsrRow_eq_decodeCsrRow csr i (h i hi)

/-- Every mathematical signed CSR input, including malformed offsets and
duplicate rows, is decoded identically by the two *pure* scanners.
This has no row-validity assumption. It is not a claim about machine
integer overflow, memory allocation, or the compiled Rust recognizer. -/
theorem rustScanSignedCsr_total_refinement (csr : SignedCsrInput) :
    rustScanSignedCsr csr = decodeSignedCsr csr := by
  apply rustScanSignedCsr_eq_decodeSignedCsr_of_row_agreement
  intro i _
  exact rustScanCsrRow_total_refinement csr i

theorem rustScanSignedCsr_total_refusal_iff (csr : SignedCsrInput) :
    rustScanSignedCsr csr = none ↔ decodeSignedCsr csr = none := by
  rw [rustScanSignedCsr_total_refinement csr]

/-- Both successful outputs and refusals of the full modeled scanner agree
on the witnessed domain. No duplicate row can disappear silently. -/
theorem rustScanSignedCsr_refusal_iff
    (csr : SignedCsrInput)
    (h : ∀ i ∈ List.range (5 * csr.variableCount - 14),
      HasRustRowSlice csr i) :
    rustScanSignedCsr csr = none ↔ decodeSignedCsr csr = none := by
  rw [rustScanSignedCsr_eq_decodeSignedCsr csr h]

/-! ## Transfer accepted counts through the Rust-shaped scanner

These declarations are about the independently defined *mathematical* CSR
scanner, not about the execution semantics of compiled Rust. They use the
total array-refinement theorem above to connect checked certificates to
complete satisfying Boolean words viewed through that scanner.
-/

/-- A certificate accepted by the independent Lean checker binds the exact
row set of the separate Rust-shaped scanner, not merely its shape. -/
theorem rustScanSignedCsr_certificate_rows
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (h : checkCsrReceipt csr ds mask = true) :
    rustScanSignedCsr csr = some (sourceRows ds) := by
  rw [rustScanSignedCsr_total_refinement]
  exact (checkCsrReceipt_fields csr ds mask h).2.1

/-- The independent Rust-shaped scanner's decoded clauses have the same
all-assignment semantics as the certified connected recurrence. -/
theorem rustScanSignedCsr_certificate_allAssignments
    (csr : SignedCsrInput) (ds : List Bool) (mask : Finset State)
    (h : checkCsrReceipt csr ds mask = true) :
    ∃ rows, rustScanSignedCsr csr = some rows ∧
      ∀ x : Nat → Bool,
      (∀ r ∈ rows,
        signedClauseEval (tripleAt x r.first r.second r.third)
          r.falsifiesAt = true) ↔
      (∀ i, i < ds.length →
        parityState (tripleAt x i (i + 1) (i + 3)) = ds[i]!) ∧
      (∀ i, i < ds.length + 1 →
        tripleAt x i (i + 1) (i + 2) ≠ zeroState) := by
  obtain ⟨rows, hd, hs⟩ := checkedCsr_allAssignments csr ds mask h
  refine ⟨rows, ?_, hs⟩
  rw [rustScanSignedCsr_total_refinement]
  exact hd

/-- Actual finite words, evaluated against the Rust-shaped mathematical
scanner rather than against a separately reconstructed canonical recurrence.
Malformed inputs have no witnesses. -/
def RustScannedCsrWords (csr : SignedCsrInput) (ds : List Bool) :=
  { w : List Bool // w.length = ds.length + 3 ∧
    ∃ rows : Finset SignedRow,
      rustScanSignedCsr csr = some rows ∧
      allRowsHold (wordAssignment w) rows }

/-- The two modeled decoders select the same finite Boolean words, including
for malformed inputs. The equivalence preserves the word unchanged. -/
def rustScannedWordsEquiv (csr : SignedCsrInput) (ds : List Bool) :
    RustScannedCsrWords csr ds ≃ DecodedCsrWords csr ds where
  toFun := fun w =>
    ⟨w.val, by
      simpa only [rustScanSignedCsr_total_refinement] using w.property⟩
  invFun := fun w =>
    ⟨w.val, by
      simpa only [rustScanSignedCsr_total_refinement] using w.property⟩
  left_inv := by
    intro w
    apply Subtype.ext
    rfl
  right_inv := by
    intro w
    apply Subtype.ext
    rfl

/-- An accepted exact count also counts the full finite words satisfying
the independent Rust-shaped CSR *semantic model*. The actual compiled
Rust recognizer-to-model refinement remains a separate obligation. -/
theorem verifiedCsr_rustScannedWordCount
    (csr : SignedCsrInput) (ds : List Bool)
    (mask : Finset State) (out : Nat)
    (h : verifyCsrCount csr ds mask = some out) :
    Nat.card (RustScannedCsrWords csr ds) = out := by
  rw [Nat.card_congr (rustScannedWordsEquiv csr ds)]
  exact verifiedCsr_decodedWordCount csr ds mask out h

#print axioms IndependentETH.NonAffine.rustScanSignedCsr_certificate_rows
#print axioms IndependentETH.NonAffine.rustScanSignedCsr_certificate_allAssignments
#print axioms IndependentETH.NonAffine.rustScannedWordsEquiv
#print axioms IndependentETH.NonAffine.verifiedCsr_rustScannedWordCount

#print axioms IndependentETH.NonAffine.rustPolarityIndex_injective
#print axioms IndependentETH.NonAffine.rustGroupingKey_injective
#print axioms IndependentETH.NonAffine.rustGroupingKey_nodup_iff
#print axioms IndependentETH.NonAffine.rustScanCsrRow_total_refinement
#print axioms IndependentETH.NonAffine.rustScanSignedCsr_total_refinement
#print axioms IndependentETH.NonAffine.rustScanSignedCsr_total_refusal_iff
#print axioms IndependentETH.NonAffine.rustScanCsrRow_eq_decodeCsrRow
#print axioms IndependentETH.NonAffine.csrRowMapM_congr
#print axioms IndependentETH.NonAffine.rustScanSignedCsr_eq_decodeSignedCsr_of_row_agreement
#print axioms IndependentETH.NonAffine.rustScanSignedCsr_eq_decodeSignedCsr
#print axioms IndependentETH.NonAffine.rustScanSignedCsr_refusal_iff

/-! ## Checked machine-word CSR shape arithmetic

This models the precise `usize` representability conditions of the shared
Rust `expected_csr_shape` helper. Unlike the preceding pure-Nat scanner,
multiplication, subtraction and the terminating-offset addition are also
proved compatible with genuinely finite `BitVec` arithmetic. The model
is parameterized by word width; it does not prove compiled Rust execution,
memory allocation, or external input parsing.
-/

/-- A Rust-shaped checked `5*n - 14` operation with explicit word bounds.
Values of `usize` are represented by Nats strictly below `2^wordBits`. -/
def checkedCsrRowCount (wordBits n : Nat) : Option Nat := do
  if n < 2 ^ wordBits && 5 * n < 2 ^ wordBits then
    if 14 ≤ 5 * n then
      some (5 * n - 14)
    else none
  else none

/-- The additional terminating offset is another checked operation. -/
def checkedCsrOffsetCount (wordBits n : Nat) : Option Nat := do
  let rows ← checkedCsrRowCount wordBits n
  if rows + 1 < 2 ^ wordBits then some (rows + 1)
  else none

/-- Successful checked multiplication for n ≥ 4 supplies the exact row count. -/
theorem checkedCsrRowCount_of_fits (wordBits n : Nat)
    (hn : 4 ≤ n) (hfit : 5 * n < 2 ^ wordBits) :
    checkedCsrRowCount wordBits n = some (5 * n - 14) := by
  have hnfit : n < 2 ^ wordBits := by omega
  have hsub : 14 ≤ 5 * n := by omega
  simp [checkedCsrRowCount, hnfit, hfit, hsub]

/-- The final offset-count increment never overflows after successful
five-fold multiplication on the supported n ≥ 4 domain. -/
theorem checkedCsrOffsetCount_of_fits (wordBits n : Nat)
    (hn : 4 ≤ n) (hfit : 5 * n < 2 ^ wordBits) :
    checkedCsrOffsetCount wordBits n = some (5 * n - 13) := by
  have hrows := checkedCsrRowCount_of_fits wordBits n hn hfit
  have hsafe : (5 * n - 14) + 1 < 2 ^ wordBits := by omega
  have hsize : (5 * n - 14) + 1 = 5 * n - 13 := by omega
  have hsafeFinal : 5 * n - 13 < 2 ^ wordBits := by omega
  simp [checkedCsrOffsetCount, hrows, hsize, hsafeFinal]

/-- A five-fold product outside the word range refuses instead of wrapping
or saturating. -/
theorem checkedCsrRowCount_overflow (wordBits n : Nat)
    (h : 2 ^ wordBits ≤ 5 * n) :
    checkedCsrRowCount wordBits n = none := by
  by_cases hn : n < 2 ^ wordBits
  · simp [checkedCsrRowCount, hn, show ¬ 5 * n < 2 ^ wordBits by omega]
  · simp [checkedCsrRowCount, hn]

/-- Any successful returned row count agrees with the exact Nat formula. -/
theorem checkedCsrRowCount_success_bounds (wordBits n rows : Nat)
    (h : checkedCsrRowCount wordBits n = some rows) :
    n < 2 ^ wordBits ∧ 5 * n < 2 ^ wordBits ∧
    14 ≤ 5 * n ∧ rows = 5 * n - 14 := by
  unfold checkedCsrRowCount at h
  split at h <;> simp_all

/-- Actual bitvector multiplication agrees with the unbounded integer
product when checked arithmetic reports that the result fits. -/
theorem checkedCsr_mul_bitvec (w n : Nat)
    (hn : 4 ≤ n) (hfit : 5 * n < 2 ^ w) :
    ((BitVec.ofNat w n) * (BitVec.ofNat w 5)).toNat = 5 * n := by
  have hnfit : n < 2 ^ w := by omega
  have hf : 5 < 2 ^ w := by omega
  rw [BitVec.toNat_mul]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnfit, Nat.mod_eq_of_lt hf]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt hfit]

/-- Subtracting fourteen in the finite word agrees with exact Nat
subtraction; no wraparound is possible in this domain. -/
theorem checkedCsr_sub_bitvec (w n : Nat)
    (hn : 4 ≤ n) (hfit : 5 * n < 2 ^ w) :
    ((BitVec.ofNat w (5 * n)) - (BitVec.ofNat w 14)).toNat =
      5 * n - 14 := by
  have hlarge : 14 ≤ 5 * n := by omega
  have hfourteen : 14 < 2 ^ w := by omega
  have hsmall : 5 * n - 14 < 2 ^ w := by omega
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit,
    Nat.mod_eq_of_lt hfourteen]
  have hrew : 2 ^ w - 14 + 5 * n = 2 ^ w + (5 * n - 14) := by omega
  rw [hrew, Nat.add_mod, Nat.mod_self]
  simp [Nat.mod_eq_of_lt hsmall]

/-- The extra terminating offset fits in the same finite word, making the
former production saturation operation unnecessary on accepted instances. -/
theorem checkedCsr_addOne_bitvec (w n : Nat)
    (hn : 4 ≤ n) (hfit : 5 * n < 2 ^ w) :
    ((BitVec.ofNat w (5 * n - 14)) + (BitVec.ofNat w 1)).toNat =
      5 * n - 13 := by
  have hrows : 5 * n - 14 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have htotal : 5 * n - 13 < 2 ^ w := by omega
  have hsize : (5 * n - 14) + 1 = 5 * n - 13 := by omega
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrows,
    Nat.mod_eq_of_lt hone]
  rw [hsize, Nat.mod_eq_of_lt htotal]

/-- On n ≥ 4, the checked offset-count calculation succeeds exactly
when the five-fold product is representable. There is no hidden failure
from subtracting fourteen or adding the terminating offset. -/
theorem checkedCsrOffsetCount_success_iff (w n : Nat) (hn : 4 ≤ n) :
    checkedCsrOffsetCount w n = some (5 * n - 13) ↔ 5 * n < 2 ^ w := by
  constructor
  · intro h
    by_cases hfit : 5 * n < 2 ^ w
    · exact hfit
    · have overflow : 2 ^ w ≤ 5 * n := by omega
      have refused := checkedCsrRowCount_overflow w n overflow
      simp [checkedCsrOffsetCount, refused] at h
  · intro hfit
    exact checkedCsrOffsetCount_of_fits w n hn hfit

/-! ## The checked per-row usize offset boundary

The shared Rust `checked_row` operation computes `start.checked_add(3)`
before reading exactly three signed literals. On a represented source
slice, equality of the two offsets with the mathematical width `3`
guarantees that this checked addition cannot overflow. These identities
bind the *arithmetic part* of the concrete Rust operation to the existing
mathematical decoder, not its compiled instructions or allocation behavior.
-/

/-- The representability check performed by Rust's `checked_add(3)`. -/
def checkedCsrRowStop (w start : Nat) : Option Nat :=
  if start < 2 ^ w && start + 3 < 2 ^ w then some (start + 3) else none

/-- Every valid, represented three-column slice passes the checked
addition. The matching second offset itself is evidence against overflow. -/
theorem checkedCsrRowStop_of_inbounds (w start stop : Nat)
    (hs : start < 2 ^ w) (ht : stop < 2 ^ w)
    (hwidth : stop = start + 3) :
    checkedCsrRowStop w start = some stop := by
  have hfit : start + 3 < 2 ^ w := by omega
  simp [checkedCsrRowStop, hs, hfit, hwidth]

/-- An overflowing mathematical row stop fails the checked operation. -/
theorem checkedCsrRowStop_overflow (w start : Nat)
    (h : 2 ^ w ≤ start + 3) : checkedCsrRowStop w start = none := by
  by_cases hs : start < 2 ^ w
  · simp [checkedCsrRowStop, hs, show ¬ start + 3 < 2 ^ w by omega]
  · simp [checkedCsrRowStop, hs]

/-- The actual finite-width `BitVec` addition agrees with the stop offset
whenever the mathematical row boundary is accepted and representable. -/
theorem checkedCsrRowStop_bitvec (w start stop : Nat)
    (hs : start < 2 ^ w) (ht : stop < 2 ^ w)
    (hwidth : stop = start + 3) :
    ((BitVec.ofNat w start) + (BitVec.ofNat w 3)).toNat = stop := by
  have hthree : 3 < 2 ^ w := by omega
  rw [BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt hthree]
  rw [← hwidth, Nat.mod_eq_of_lt ht]

/-! ## Concrete checked three-element CSR row model

This is an explicit model of the *operations* in production Rust's
SignedCsr::checked_row, rather than a claim about the compiled Rust binary.
It models checked row+1/start+3 arithmetic, get(start..stop), converting
that slice to an array of three elements, and the shared polarity/column
predicate. Unlike a model made solely from three independent get calls,
the checkedSlice3 definition uses an actual list slice and a length-three
match. The equivalence below proves that this distinction does not change
acceptance or refusal.

The theorem is conditional only on the fact that the in-memory offsets and
their list length are representable as machine words. The real Rust type
usize supplies these assumptions, while compiler execution correspondence
and heap/collection semantics remain separate obligations.
-/

variable {α : Type}

/-- The exact three-element data returned by a valid list slice. -/
theorem take_drop_three (xs : List α) (start : Nat)
    (h : start + 3 ≤ xs.length) :
    (xs.drop start).take 3 = [xs[start], xs[start + 1], xs[start + 2]] := by
  have h0 : start < xs.length := by omega
  have h1 : start + 1 < xs.length := by omega
  have h2 : start + 2 < xs.length := by omega
  rw [List.drop_eq_getElem_cons h0]
  rw [List.drop_eq_getElem_cons h1]
  rw [List.drop_eq_getElem_cons h2]
  simp only [List.take]

/-- Model Rust's checked get(start..stop) followed by [T; 3] conversion,
once the caller has established stop = start+3. -/
def checkedSlice3 (xs : List α) (start : Nat) : Option (α × α × α) :=
  if start + 3 ≤ xs.length then
    match (xs.drop start).take 3 with
    | [a, b, c] => some (a, b, c)
    | _ => none
  else none

/-- Elementwise checked reads, independent of the slice representation. -/
def indexedTriple (xs : List α) (start : Nat) : Option (α × α × α) := do
  let a ← xs[start]?
  let b ← xs[start + 1]?
  let c ← xs[start + 2]?
  pure (a, b, c)

/-- A checked three-element slice is equivalent to three checked indexed
reads, including when its final read would be out of bounds. -/
theorem checkedSlice3_eq_indexedTriple (xs : List α) (start : Nat) :
    checkedSlice3 xs start = indexedTriple xs start := by
  by_cases h : start + 3 ≤ xs.length
  · have h0 : start < xs.length := by omega
    have h1 : start + 1 < xs.length := by omega
    have h2 : start + 2 < xs.length := by omega
    simp [checkedSlice3, h, indexedTriple, take_drop_three xs start h,
      List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2]
  · have h2 : xs[start + 2]? = none := List.getElem?_eq_none (by omega)
    simp [checkedSlice3, h, indexedTriple, h2]

/-- The checked index increment in Rust's offsets.get(row.checked_add(1)?). -/
def checkedUsizeSucc (w i : Nat) : Option Nat :=
  if i + 1 < 2 ^ w then some (i + 1) else none

/-- If the offset array's length fits in w bits, an overflowing row+1
cannot index an actual element, so both checked and unbounded reads refuse. -/
theorem checkedUsizeSucc_lookup (w i : Nat) (offsets : List Nat)
    (hbounded : offsets.length ≤ 2 ^ w) :
    (do let j ← checkedUsizeSucc w i; offsets[j]?) = offsets[i + 1]? := by
  by_cases h : i + 1 < 2 ^ w
  · simp [checkedUsizeSucc, h]
  · have hoob : offsets[i + 1]? = none := List.getElem?_eq_none (by omega)
    simp [checkedUsizeSucc, h, hoob]

/-- Rust checked_row in a pure, width-parametric operational model:
checked row index, checked end offset, two range reads converted to triples,
then exactly the same validated-sign/column predicate as the production
CheckedCsrRow constructor. The returned SignedRow is semantic, not ABI data. -/
def machineCheckedRow (w : Nat) (csr : SignedCsrInput) (i : Nat) :
    Option SignedRow := do
  let start ← csr.offsets[i]?
  let next ← checkedUsizeSucc w i
  let stop ← csr.offsets[next]?
  let expectedStop ← checkedCsrRowStop w start
  if stop != expectedStop then none else
    let (a, b, c) ← checkedSlice3 csr.columns start
    let (sa, sb, sc) ← checkedSlice3 csr.signs start
    rustTripleRow csr.variableCount a b c sa sb sc

/-- For observed, representable offsets with width three, every concrete
checked-slice acceptance and refusal agrees with the existing scanner. -/
theorem machineCheckedRow_of_valid_offsets (w : Nat)
    (csr : SignedCsrInput) (i start stop : Nat)
    (hs : csr.offsets[i]? = some start)
    (he : csr.offsets[i + 1]? = some stop)
    (hi : i + 1 < 2 ^ w)
    (hsfit : start < 2 ^ w)
    (hefit : stop < 2 ^ w)
    (hw : stop = start + 3) :
    machineCheckedRow w csr i = rustScanCsrRow csr i := by
  have hsum : start + 3 < 2 ^ w := by omega
  by_cases hb : stop ≤ csr.columns.length
  · have hb' : start + 3 ≤ csr.columns.length := by omega
    simp [machineCheckedRow, rustScanCsrRow, checkedUsizeSucc, checkedCsrRowStop,
      hs, he, hi, hsfit, hsum, hw,
      checkedSlice3_eq_indexedTriple, indexedTriple, hb', Option.bind_assoc]
  · have hfail : checkedSlice3 csr.columns start = none := by
      simp [checkedSlice3, show ¬ start + 3 ≤ csr.columns.length by omega]
    simp [machineCheckedRow, rustScanCsrRow, checkedUsizeSucc, checkedCsrRowStop,
      hs, he, hi, hsfit, hsum, hw, hfail,
      show ¬ start + 3 ≤ csr.columns.length by omega]

/-- Wrong-width rows refuse identically, even if start+3 would overflow
usize and no slice is ever touched. -/
theorem machineCheckedRow_of_wrong_width (w : Nat)
    (csr : SignedCsrInput) (i start stop : Nat)
    (hs : csr.offsets[i]? = some start)
    (he : csr.offsets[i + 1]? = some stop)
    (hi : i + 1 < 2 ^ w)
    (hsfit : start < 2 ^ w)
    (hw : stop ≠ start + 3) :
    machineCheckedRow w csr i = rustScanCsrRow csr i := by
  have hbad :
      ¬(start ≤ stop ∧ stop ≤ csr.columns.length ∧ stop - start = 3) := by
    omega
  by_cases hsum : start + 3 < 2 ^ w
  · simp [machineCheckedRow, rustScanCsrRow, checkedUsizeSucc, checkedCsrRowStop,
      hs, he, hi, hsfit, hsum, hw, hbad]
  · simp [machineCheckedRow, rustScanCsrRow, checkedUsizeSucc, checkedCsrRowStop,
      hs, he, hi, hsfit, hsum, hbad]

/-- The two row decoders have identical Option outcomes for every row and
every malformed offset, provided the offsets live in the represented
machine-word domain. Neither well-formedness nor success is assumed. -/
theorem machineCheckedRow_total_refinement (w : Nat)
    (csr : SignedCsrInput) (i : Nat)
    (hOffsets : csr.offsets.length ≤ 2 ^ w)
    (hValues : ∀ (j z : Nat), csr.offsets[j]? = some z → z < 2 ^ w) :
    machineCheckedRow w csr i = rustScanCsrRow csr i := by
  cases hs : csr.offsets[i]? with
  | none => simp [machineCheckedRow, rustScanCsrRow, hs]
  | some start =>
    by_cases hi : i + 1 < 2 ^ w
    · cases he : csr.offsets[i + 1]? with
      | none =>
        simp [machineCheckedRow, rustScanCsrRow, checkedUsizeSucc, hs, he, hi]
      | some stop =>
        have hsfit := hValues i start hs
        have hefit := hValues (i + 1) stop he
        by_cases hw : stop = start + 3
        · exact machineCheckedRow_of_valid_offsets w csr i start stop
            hs he hi hsfit hefit hw
        · exact machineCheckedRow_of_wrong_width w csr i start stop
            hs he hi hsfit hw
    · have hmiss : csr.offsets[i + 1]? = none :=
        List.getElem?_eq_none (by omega)
      simp [machineCheckedRow, rustScanCsrRow, checkedUsizeSucc, hs, hi, hmiss]

/-- Exact full-row correspondence with the *original* Lean decoder,
including both successful rows and malformed-input refusal. This is
conditional on representation as finite machine words, not on source
satisfiability or the recurrence restriction. -/
theorem machineCheckedRow_eq_decodeCsrRow (w : Nat)
    (csr : SignedCsrInput) (i : Nat)
    (hOffsets : csr.offsets.length ≤ 2 ^ w)
    (hValues : ∀ (j z : Nat), csr.offsets[j]? = some z → z < 2 ^ w) :
    machineCheckedRow w csr i = decodeCsrRow csr i := by
  rw [machineCheckedRow_total_refinement w csr i hOffsets hValues]
  exact rustScanCsrRow_total_refinement csr i

#print axioms IndependentETH.NonAffine.checkedSlice3_eq_indexedTriple
#print axioms IndependentETH.NonAffine.checkedUsizeSucc_lookup
#print axioms IndependentETH.NonAffine.machineCheckedRow_total_refinement
#print axioms IndependentETH.NonAffine.machineCheckedRow_eq_decodeCsrRow

#print axioms IndependentETH.NonAffine.checkedCsrRowStop_of_inbounds
#print axioms IndependentETH.NonAffine.checkedCsrRowStop_overflow
#print axioms IndependentETH.NonAffine.checkedCsrRowStop_bitvec

#print axioms IndependentETH.NonAffine.checkedCsrRowCount_of_fits
#print axioms IndependentETH.NonAffine.checkedCsrOffsetCount_success_iff
#print axioms IndependentETH.NonAffine.checkedCsrOffsetCount_of_fits
#print axioms IndependentETH.NonAffine.checkedCsrRowCount_overflow
#print axioms IndependentETH.NonAffine.checkedCsrRowCount_success_bounds
#print axioms IndependentETH.NonAffine.checkedCsr_mul_bitvec
#print axioms IndependentETH.NonAffine.checkedCsr_sub_bitvec
#print axioms IndependentETH.NonAffine.checkedCsr_addOne_bitvec

end IndependentETH.NonAffine
