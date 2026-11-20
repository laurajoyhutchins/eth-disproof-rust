import Mathlib

/-!
# Quadratic Boolean functions are determined by Hamming-weight ≤ 2 samples

A Boolean assignment is identified with the finite set of coordinates
on which it equals one. Degree-two squarefree polynomials over ZMod 2
have a constant, independent linear coefficients, and independent
quadratic coefficients only on ordered pairs.

This proves *mathematical* uniqueness of reconstruction from zero,
singleton, and doubleton samples. Native Rust code and its sample-budget
logic require a separate implementation-correspondence proof.
-/

namespace IndependentETH.QuadraticLowWeight

open scoped BigOperators

/-- A squarefree degree-two polynomial with no duplicate pair coefficients. -/
structure Coeff (α : Type*) where
  constant : ZMod 2
  linear : α → ZMod 2
  pair : α → α → ZMod 2

/-- A finite subset is the support of a Boolean assignment. -/
def Coeff.eval {α : Type*} [LinearOrder α]
    (p : Coeff α) (support : Finset α) : ZMod 2 :=
  p.constant + (∑ i ∈ support, p.linear i) +
    (∑ i ∈ support, ∑ j ∈ support,
      if i < j then p.pair i j else 0)

@[simp] theorem eval_empty {α : Type*} [LinearOrder α]
    (p : Coeff α) : p.eval ∅ = p.constant := by
  simp [Coeff.eval]

@[simp] theorem eval_singleton {α : Type*} [LinearOrder α]
    (p : Coeff α) (i : α) : p.eval {i} = p.constant + p.linear i := by
  simp [Coeff.eval]

/-- Evaluating a two-element support isolates one ordered quadratic coefficient. -/
theorem eval_pair {α : Type*} [LinearOrder α]
    (p : Coeff α) (i j : α) (hij : i < j) :
    p.eval ({i, j} : Finset α) =
      p.constant + p.linear i + p.linear j + p.pair i j := by
  have hne : i ≠ j := ne_of_lt hij
  have hnot : ¬ j < i := not_lt_of_ge (le_of_lt hij)
  simp [Coeff.eval, hne, Ne.symm hne, hij, hnot,
    add_assoc, add_left_comm, add_comm]

/-- Recover a linear coefficient from its singleton and empty samples. -/
theorem linear_from_samples {α : Type*} [LinearOrder α]
    (p : Coeff α) (i : α) :
    p.linear i = p.eval {i} - p.eval ∅ := by
  simp [eval_singleton, eval_empty]

/-- Recover an ordered pair coefficient from zero-, one-, and two-bit samples. -/
theorem pair_from_samples {α : Type*} [LinearOrder α]
    (p : Coeff α) (i j : α) (hij : i < j) :
    p.pair i j =
      p.eval ({i, j} : Finset α) - p.eval {i} -
        p.eval {j} + p.eval ∅ := by
  rw [eval_pair p i j hij, eval_singleton, eval_singleton, eval_empty]
  ring

/-- Equality at zero, singleton and doubleton supports entails equality
at *every* Boolean assignment, regardless of the number of coordinates. -/
theorem ext_of_low_weight_samples {α : Type*} [LinearOrder α]
    (p q : Coeff α)
    (hzero : p.eval ∅ = q.eval ∅)
    (hone : ∀ i : α, p.eval {i} = q.eval {i})
    (htwo : ∀ i j : α, i < j →
      p.eval ({i, j} : Finset α) = q.eval ({i, j} : Finset α))
    (support : Finset α) :
    p.eval support = q.eval support := by
  have hc : p.constant = q.constant := by
    simpa only [eval_empty] using hzero
  have hl : ∀ i : α, p.linear i = q.linear i := by
    intro i
    rw [linear_from_samples p i, linear_from_samples q i,
      hone i, hzero]
  have hp : ∀ i j : α, i < j → p.pair i j = q.pair i j := by
    intro i j hij
    rw [pair_from_samples p i j hij, pair_from_samples q i j hij,
      htwo i j hij, hone i, hone j, hzero]
  have hlinear :
      (∑ i ∈ support, p.linear i) =
        (∑ i ∈ support, q.linear i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hl i
  have hpairs :
      (∑ i ∈ support, ∑ j ∈ support,
        if i < j then p.pair i j else 0) =
      (∑ i ∈ support, ∑ j ∈ support,
        if i < j then q.pair i j else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp [h, hp i j h]
    · simp [h]
  unfold Coeff.eval
  rw [hc, hlinear, hpairs]


/-!
## Executable low-weight certificate and signed local witness boundary

This refines the mathematical finite-sample equality test into a Boolean
checker over the exact coefficient type. Its accepted result is an
all-context equality witness. It does NOT prove the native Rust decoder,
allocator, interpolation loop or row interpreter implements this checker.
-/

/-- Executable comparison of all weight-zero, one and two samples.
Finite quantifiers are over Fin n, not the powerset of its assignments. -/
def checkSamples {n : ℕ} (expected claimed : Coeff (Fin n)) : Bool :=
  decide (
    expected.eval ∅ = claimed.eval ∅ ∧
    (∀ i : Fin n, expected.eval {i} = claimed.eval {i}) ∧
    (∀ i j : Fin n, i < j →
      expected.eval ({i, j} : Finset (Fin n)) =
        claimed.eval ({i, j} : Finset (Fin n))))

/-- Acceptance constructs the precise all-boundary equality needed for an
integer-valued local signed-elimination witness. -/
theorem checkSamples_sound {n : ℕ} (expected claimed : Coeff (Fin n))
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    expected.eval support = claimed.eval support := by
  have h :
      expected.eval ∅ = claimed.eval ∅ ∧
      (∀ i : Fin n, expected.eval {i} = claimed.eval {i}) ∧
      (∀ i j : Fin n, i < j →
        expected.eval ({i, j} : Finset (Fin n)) =
          claimed.eval ({i, j} : Finset (Fin n))) := by
    simpa only [checkSamples, decide_eq_true_eq] using accepted
  exact ext_of_low_weight_samples expected claimed h.1 h.2.1 h.2.2 support

/-- Every valid coefficient pair passes the executable sample checker. -/
theorem checkSamples_complete {n : ℕ} (p : Coeff (Fin n)) :
    checkSamples p p = true := by
  simp [checkSamples]

/-- Integer semantics of a Boolean sign, distinct from GF(2) arithmetic. -/
def signedBit (phase : Bool) : ℤ := if phase = true then -1 else 1

/-- Read one GF(2) coefficient evaluation as a Boolean phase bit. -/
def phaseBit {n : ℕ} (p : Coeff (Fin n))
    (support : Finset (Fin n)) : Bool :=
  decide (p.eval support = 1)

/-- A checked low-weight certificate also preserves the exact integer sign. -/
theorem checkSamples_sign_sound {n : ℕ}
    (expected claimed : Coeff (Fin n))
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    signedBit (phaseBit expected support) =
      signedBit (phaseBit claimed support) := by
  have h := checkSamples_sound expected claimed accepted support
  simp [phaseBit, h]

/-- Algebraic signed cancellation used by the free-variable receipt.
Proof uses all four Boolean cases, not probabilistic sampling. -/
private theorem signedBoolFiber (a ell : Bool) :
    (∑ x : Bool, signedBit (a ^^ (x && ell))) =
      if ell = true then 0 else 2 * signedBit a := by
  cases a <;> cases ell <;> decide

/-- When the source has the stipulated quadratic/affine split, a checked
low-weight phase certificate and the exact cancellation constraint imply
the correct integer-valued free-variable elimination at *every* boundary.

The split hypothesis is a typed source semantic obligation; Rust source-
phase normalization must eventually be proved to instantiate it.
-/
theorem checkedFreeLocalExact {n : ℕ}
    (sourcePhase : Bool → Finset (Fin n) → Bool)
    (expected claimed : Coeff (Fin n))
    (mixed feasible : Finset (Fin n) → Bool)
    (k : ℕ)
    (hsource : ∀ x support,
      sourcePhase x support =
        (phaseBit expected support ^^ (x && mixed support)))
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    (∑ x : Bool, if feasible support = true then
       (2 : ℤ) ^ k * signedBit (sourcePhase x support) else 0) =
      (if (feasible support && !(mixed support)) = true then
        (2 : ℤ) ^ (k + 1) * signedBit (phaseBit claimed support)
      else 0) := by
  have hphase : expected.eval support = claimed.eval support :=
    checkSamples_sound expected claimed accepted support
  have hbit : phaseBit expected support = phaseBit claimed support := by
    simp [phaseBit, hphase]
  rw [← hbit]
  simp only [hsource]
  cases hf : feasible support <;>
    cases hm : mixed support <;>
    cases hp : phaseBit expected support <;>
    simp [hf, hm, hp, signedBit, pow_succ] <;> ring

/-- A forced internal variable has exactly one feasible extension. The
checked quadratic phase must match the source at that forced value. -/
theorem checkedForcedLocalExact {n : ℕ}
    (sourcePhase : Bool → Finset (Fin n) → Bool)
    (expected claimed : Coeff (Fin n))
    (forced feasible : Finset (Fin n) → Bool)
    (k : ℕ)
    (hsource : ∀ support,
      sourcePhase (forced support) support = phaseBit expected support)
    (accepted : checkSamples expected claimed = true)
    (support : Finset (Fin n)) :
    (∑ x : Bool, if (x == forced support) && feasible support then
       (2 : ℤ) ^ k * signedBit (sourcePhase x support) else 0) =
      (if feasible support = true then
        (2 : ℤ) ^ k * signedBit (phaseBit claimed support) else 0) := by
  have hphase : expected.eval support = claimed.eval support :=
    checkSamples_sound expected claimed accepted support
  have hbit : phaseBit expected support = phaseBit claimed support := by
    simp [phaseBit, hphase]
  rw [← hbit]
  calc
    (∑ x : Bool, if (x == forced support) && feasible support then
       (2 : ℤ) ^ k * signedBit (sourcePhase x support) else 0) =
        (if feasible support = true then
          (2 : ℤ) ^ k * signedBit (sourcePhase (forced support) support)
        else 0) := by
          cases hf : feasible support <;> cases hx : forced support <;>
            simp [hf, hx, Fintype.sum_bool]
    _ = _ := by rw [hsource support]

/-!
## Sparse native-record model (a typed specification, not Rust FFI refinement)

Rust's QuadraticCoefficientWitness stores a Boolean constant, a fixed-width
linear vector and lexicographically increasing in-range pairs of usize indices.
This executable Lean model stores the same *logical* fields as lists of Nat
indices. It checks their shape before decoding into Coeff (Fin n).
It does not assert that Rust memory, usize, serde or the checker control flow
implements this Lean model; those correspondences remain separate obligations.
-/

/-- Logical shape of the native sparse quadratic coefficient receipt. -/
structure SparseCoefficientRecord where
  constant : Bool
  linear : List Bool
  orderedPairs : List (Nat × Nat)
deriving Repr, DecidableEq

/-- Strict lexicographic order on the pair representation used by Rust. -/
def pairBefore (a b : Nat × Nat) : Bool :=
  decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))

/-- Adjacent-pair monotonicity is the exact native Rust previous-pair check.
Since lexicographic order is transitive, this excludes all duplicates and
reorderings; no undecidable Pairwise relation is needed to compute it. -/
def sparsePairsInOrder (pairs : List (Nat × Nat)) : Bool :=
  (pairs.zip (pairs.drop 1)).all (fun p => pairBefore p.1 p.2)

/-- Decide whether the native sparse coefficient record satisfies its shape contract. -/
def SparseCoefficientRecord.checkShape (r : SparseCoefficientRecord) (n : ℕ) : Bool :=
  decide (r.linear.length = n) &&
    r.orderedPairs.all (fun p => decide (p.1 < p.2 ∧ p.2 < n)) &&
    sparsePairsInOrder r.orderedPairs

/-- Acceptance is the executable structural predicate, not an oracle. -/
def SparseCoefficientRecord.wellFormed (r : SparseCoefficientRecord) (n : ℕ) : Prop :=
  r.checkShape n = true

/-- Acceptance by the structural checker implies the exact well-formedness predicate. -/
theorem SparseCoefficientRecord.checkShape_sound
    (r : SparseCoefficientRecord) (n : ℕ)
    (accepted : r.checkShape n = true) : r.wellFormed n :=
  accepted

theorem SparseCoefficientRecord.checkShape_width
    (r : SparseCoefficientRecord) (n : ℕ)
    (accepted : r.checkShape n = true) : r.linear.length = n := by
  simp only [SparseCoefficientRecord.checkShape, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  exact accepted.1.1

/-- Total logical decoding; use only a shape-checked record for native claims.
The Option fallback keeps this model total on malformed lists, while checkShape
refuses their use as a valid native certificate. -/
def SparseCoefficientRecord.decode (r : SparseCoefficientRecord) (n : ℕ) :
    Coeff (Fin n) where
  constant := if r.constant then 1 else 0
  linear := fun i => if (r.linear[i.val]?).getD false then 1 else 0
  pair := fun i j => if (i.val, j.val) ∈ r.orderedPairs then 1 else 0

/-- A directly stated ZMod 2 interpretation of the record's bits.
This is not yet a proof about Rust's sequence of XOR instructions. -/
def SparseCoefficientRecord.evalZMod (r : SparseCoefficientRecord) (n : ℕ)
    (support : Finset (Fin n)) : ZMod 2 :=
  (if r.constant then 1 else 0) +
    (∑ i ∈ support, if (r.linear[i.val]?).getD false then 1 else 0) +
    (∑ i ∈ support, ∑ j ∈ support,
      if i < j then
        (if (i.val, j.val) ∈ r.orderedPairs then 1 else 0)
      else 0)

/-- Decoding a record preserves its direct modular polynomial interpretation. -/
theorem SparseCoefficientRecord.decode_eval (r : SparseCoefficientRecord) (n : ℕ)
    (support : Finset (Fin n)) :
    (r.decode n).eval support = r.evalZMod n support := by
  rfl

/-- Apply the existing low-weight theorem to well-shaped sparse records. -/
def checkSparseSamples {n : ℕ}
    (expected claimed : SparseCoefficientRecord) : Bool :=
  expected.checkShape n &&
    (claimed.checkShape n &&
      checkSamples (expected.decode n) (claimed.decode n))

/-- Accepted sparse-record samples agree as integer signs on every boundary support. -/
theorem checkSparseSamples_sign_sound {n : ℕ}
    (expected claimed : SparseCoefficientRecord)
    (accepted : checkSparseSamples (n := n) expected claimed = true)
    (support : Finset (Fin n)) :
    signedBit (phaseBit (expected.decode n) support) =
      signedBit (phaseBit (claimed.decode n) support) := by
  simp only [checkSparseSamples, Bool.and_eq_true] at accepted
  exact checkSamples_sign_sound _ _ accepted.2.2 support

/-- XOR on Boolean bits is addition modulo two, exactly, not heuristically. -/
def boolZMod (bit : Bool) : ZMod 2 := if bit then 1 else 0

/-- Boolean XOR is addition in the two-element coefficient ring. -/
theorem boolZMod_xor (a b : Bool) :
    boolZMod (a ^^ b) = boolZMod a + boolZMod b := by
  cases a <;> cases b <;> decide

/-- The Rust-style left XOR-fold agrees with the modular sum of input bits. -/
theorem xorFold_eq_zmod_sum (acc : Bool) (bits : List Bool) :
    boolZMod (bits.foldl (fun x y => x ^^ y) acc) =
      boolZMod acc + (bits.map boolZMod).sum := by
  induction bits generalizing acc with
  | nil =>
      simp
  | cons b bs ih =>
      change boolZMod (bs.foldl (fun x y => x ^^ y) (acc ^^ b)) =
        boolZMod acc + (boolZMod b + (bs.map boolZMod).sum)
      rw [ih, boolZMod_xor]
      ring

example :
    (SparseCoefficientRecord.checkShape
      { constant := false, linear := [true, false],
        orderedPairs := [(0, 1)] } 2) = true := by decide

example :
    (SparseCoefficientRecord.checkShape
      { constant := false, linear := [true, false],
        orderedPairs := [(1, 0)] } 2) = false := by decide

example :
    (SparseCoefficientRecord.checkShape
      { constant := false, linear := [true, false],
        orderedPairs := [(0, 1), (0, 1)] } 2) = false := by decide

/-!
## Independent, exhaustive native-record acceptance oracle

This checker interprets raw zero-based source and output monomial lists and
affine row-index lists, rather than trusting a producer's normalized phase.
It is deliberately exponential in the number of boundary bits: it closes
the *instance-level semantic acceptance* boundary, not the polynomial-time
native verifier refinement or any ETH complexity claim.

Coordinate 0 of a source is the internal bit, and coordinates 1..n are
the exterior ports. Output coordinates are 0..n-1. A converter from native
Rust data must faithfully serialize these fields; that converter is outside
this Lean kernel theorem's trust boundary.
-/

/-- Raw source phase, affine constraints, and power-of-two coefficient. -/
structure NativeSourceRecord where
  phaseTerms : List (List Nat)
  rows : List (List Nat × Bool)
  exponent : Nat
deriving Repr

/-- Raw projected phase, affine constraints, optional row, and coefficient receipt. -/
structure NativeOutputRecord where
  phaseTerms : List (List Nat)
  rows : List (List Nat × Bool)
  added : Option (List Nat × Bool)
  exponent : Nat
  receipt : SparseCoefficientRecord
deriving Repr

/-- Native Rust style XOR of the named coordinate occurrences. -/
def nativeXorRow (bits : Nat → Bool) (indices : List Nat) : Bool :=
  indices.foldl (fun parity index => parity ^^ bits index) false

/-- Native Rust style ANF evaluation: conjunction inside a monomial,
XOR across monomials. This remains defined even on malformed raw data. -/
def nativePhase (bits : Nat → Bool) (terms : List (List Nat)) : Bool :=
  terms.foldl (fun parity term => parity ^^ term.all bits) false

/-!
## Abstract normalization of the native quadratic constructor

The Rust constructor sorts each monomial, removes repeated coordinate
indices, and toggles its membership in a BTreeSet. We use a finite set
of coordinates for each monomial and a finite set of surviving
monomials. This avoids depending on any particular sorting algorithm
or container layout, while preserving the mathematical shape and
toggle semantics of successful construction.

A separate execution refinement is still needed for Rust collection
methods, memory allocation, and rejection order.
-/

/-- The squarefree support of a raw monomial, retaining idempotent Boolean multiplication. -/
def canonicalTerm (term : List ℕ) : Finset ℕ :=
  term.toFinset

/-- Abstract BTreeSet toggle: insertion creates an absent term and
insertion of an already present term cancels it modulo two. -/
def toggleCanonical (state : Finset (Finset ℕ)) (term : Finset ℕ) :
    Finset (Finset ℕ) :=
  if term ∈ state then state.erase term else insert term state

/-- Normalize all raw monomials using the native XOR-cancellation rule. -/
def canonicalizeTerms (raw : List (List ℕ)) : Finset (Finset ℕ) :=
  raw.foldl (fun state term => toggleCanonical state (canonicalTerm term)) ∅

/-- Integer-ring interpretation of a squarefree monomial's Boolean value. -/
def canonicalTermValue (bits : ℕ → Bool) (term : Finset ℕ) : ZMod 2 :=
  if ∀ i ∈ term, bits i = true then 1 else 0

/-- Evaluate only surviving canonical monomials, once each. -/
def canonicalPhaseValue (bits : ℕ → Bool) (state : Finset (Finset ℕ)) : ZMod 2 :=
  state.sum (canonicalTermValue bits)

/-- Sorting and deduplicating a raw monomial leaves its Boolean product unchanged. -/
theorem canonicalTerm_value (bits : ℕ → Bool) (term : List ℕ) :
    canonicalTermValue bits (canonicalTerm term) =
      boolZMod (term.all bits) := by
  classical
  have h : (∀ i ∈ canonicalTerm term, bits i = true) ↔
      term.all bits = true := by
    simp [canonicalTerm, List.all_eq_true]
  cases hv : term.all bits with
  | false =>
      have hn : ¬ ∀ i ∈ canonicalTerm term, bits i = true := by
        intro ht
        have htrue := h.mp ht
        simp [hv] at htrue
      simp [canonicalTermValue, boolZMod, hv, hn]
  | true =>
      have ht : ∀ i ∈ canonicalTerm term, bits i = true :=
        h.mpr (by simp [hv])
      simp [canonicalTermValue, boolZMod, hv, ht]

/-- A single set toggle adds exactly one monomial contribution modulo two. -/
theorem toggleCanonical_value (bits : ℕ → Bool)
    (state : Finset (Finset ℕ)) (term : Finset ℕ) :
    canonicalPhaseValue bits (toggleCanonical state term) =
      canonicalPhaseValue bits state + canonicalTermValue bits term := by
  classical
  by_cases h : term ∈ state
  · have hsum : canonicalPhaseValue bits state =
        canonicalTermValue bits term +
          canonicalPhaseValue bits (state.erase term) := by
      calc
        canonicalPhaseValue bits state =
            canonicalPhaseValue bits (insert term (state.erase term)) := by
              exact congrArg (canonicalPhaseValue bits) (Finset.insert_erase h).symm
        _ = canonicalTermValue bits term +
            canonicalPhaseValue bits (state.erase term) := by
              simp [canonicalPhaseValue]
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      canonicalPhaseValue bits (toggleCanonical state term) =
          canonicalPhaseValue bits (state.erase term) := by
            simp [toggleCanonical, h]
      _ = (2 : ZMod 2) * canonicalTermValue bits term +
            canonicalPhaseValue bits (state.erase term) := by simp [htwo]
      _ = (canonicalTermValue bits term +
            canonicalPhaseValue bits (state.erase term)) +
            canonicalTermValue bits term := by ring
      _ = canonicalPhaseValue bits state + canonicalTermValue bits term := by rw [hsum]
  · calc
      canonicalPhaseValue bits (toggleCanonical state term) =
          canonicalTermValue bits term + canonicalPhaseValue bits state := by
            simp [toggleCanonical, h, canonicalPhaseValue]
      _ = canonicalPhaseValue bits state + canonicalTermValue bits term := by ring

private theorem canonicalize_fold_value (bits : ℕ → Bool)
    (raw : List (List ℕ)) (initial : Finset (Finset ℕ)) :
    canonicalPhaseValue bits
      (raw.foldl (fun state term =>
        toggleCanonical state (canonicalTerm term)) initial) =
      canonicalPhaseValue bits initial +
        (raw.map (fun term => canonicalTermValue bits (canonicalTerm term))).sum := by
  induction raw generalizing initial with
  | nil =>
      simp
  | cons term rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, toggleCanonical_value]
      ring

/-- The exact native constructor's abstract canonicalization preserves
the raw XOR-of-products value for arbitrary monomials and assignments.

This proof is independent of input order and duplicates. The ZMod 2
interpretation is equivalent to Boolean XOR via boolZMod. -/
theorem canonicalization_value (bits : ℕ → Bool) (raw : List (List ℕ)) :
    canonicalPhaseValue bits (canonicalizeTerms raw) =
      boolZMod (nativePhase bits raw) := by
  calc
    canonicalPhaseValue bits (canonicalizeTerms raw) =
        (raw.map (fun term => canonicalTermValue bits (canonicalTerm term))).sum := by
          simpa [canonicalizeTerms, canonicalPhaseValue] using
            canonicalize_fold_value bits raw (∅ : Finset (Finset ℕ))
    _ = (raw.map (fun term => boolZMod (term.all bits))).sum := by
          simp only [canonicalTerm_value]
    _ = boolZMod (nativePhase bits raw) := by
          simpa [nativePhase, boolZMod, List.map_map, Function.comp_def] using
            (xorFold_eq_zmod_sum false (raw.map (fun term => term.all bits))).symm

/-- Native constructor acceptance, stated over the mathematical width.
Rust's usize representability and allocation are separate obligations.
The cardinality test follows sorting and idempotent deduplication. -/
def nativeConstructorOK (width : ℕ) (raw : List (List ℕ)) : Bool :=
  raw.all (fun term =>
    term.all (fun i => decide (i < width)) &&
      decide ((canonicalTerm term).card ≤ 2))

/-- Accepted constructor inputs contain only in-range coordinates and
squarefree supports with at most two distinct indices. -/
theorem nativeConstructorOK_sound (width : ℕ) (raw : List (List ℕ))
    (h : nativeConstructorOK width raw = true) :
    ∀ term ∈ raw,
      (∀ i ∈ term, i < width) ∧ (canonicalTerm term).card ≤ 2 := by
  simp only [nativeConstructorOK, List.all_eq_true,
    Bool.and_eq_true, decide_eq_true_eq] at h
  intro term hmem
  have ht := h term hmem
  constructor
  · intro i himem
    have hbits := List.all_eq_true.mp ht.1 i himem
    exact of_decide_true hbits
  · exact ht.2

/-- Mathematical accepted-or-refused constructor, with no partial state exposed. -/
def nativeConstruct (width : ℕ) (raw : List (List ℕ)) :
    Option (Finset (Finset ℕ)) :=
  if nativeConstructorOK width raw = true then
    some (canonicalizeTerms raw)
  else none

/-- Any accepted constructor result retains the original raw phase semantics. -/
theorem nativeConstruct_sound (width : ℕ) (raw : List (List ℕ))
    (result : Finset (Finset ℕ))
    (h : nativeConstruct width raw = some result)
    (bits : ℕ → Bool) :
    canonicalPhaseValue bits result = boolZMod (nativePhase bits raw) := by
  by_cases hshape : nativeConstructorOK width raw = true
  · have hr : canonicalizeTerms raw = result := by
      simpa [nativeConstruct, hshape] using h
    rw [← hr]
    exact canonicalization_value bits raw
  · simp [nativeConstruct, hshape] at h

/-- Invalid monomials are refused before a result is constructed. -/
theorem nativeConstruct_refuses (width : ℕ) (raw : List (List ℕ))
    (h : nativeConstructorOK width raw = false) :
    nativeConstruct width raw = none := by
  simp [nativeConstruct, h]

example : nativeConstructorOK 2 [[0, 0], [1, 0]] = true := by decide
example : nativeConstructorOK 2 [[2]] = false := by decide
example : nativeConstructorOK 3 [[0, 1, 2]] = false := by decide
example : nativeConstruct 2 [[0], [0]] = some ∅ := by decide

/-- Map source coordinate zero to the internal bit and later coordinates to boundary bits. -/
def nativeSourceBit {n : ℕ} (x : Bool) (boundary : Fin n → Bool)
    (index : Nat) : Bool :=
  if index == 0 then x else ((List.ofFn boundary)[index - 1]?).getD false

/-- Interpret projected coordinates directly in the boundary assignment. -/
def nativeOutputBit {n : ℕ} (boundary : Fin n → Bool)
    (index : Nat) : Bool :=
  ((List.ofFn boundary)[index]?).getD false

/-!
## Source-derived internal-bit phase splitting

This models the Boolean multiplication/XOR behavior of the native
`QuadraticPhase::remove_first` operation before interpolation. The
definition works even for repeated or malformed raw monomials, so the
algebraic identity does not rely on normalization or bounded width.
It is a specification-level theorem, not Rust execution refinement.
-/

/-- Evaluate a source monomial with coordinate zero omitted from the product. -/
def nativeTermTail {n : ℕ} (boundary : Fin n → Bool) (term : List Nat) : Bool :=
  term.all (fun index =>
    if index == 0 then true else nativeOutputBit boundary (index - 1))

/-- Each raw source monomial is a boundary product times its optional internal bit. -/
theorem nativeTerm_split {n : ℕ} (boundary : Fin n → Bool)
    (term : List Nat) (x : Bool) :
    term.all (nativeSourceBit x boundary) =
      (nativeTermTail boundary term &&
        (if term.contains 0 then x else true)) := by
  induction term with
  | nil =>
      simp [nativeTermTail]
  | cons index rest ih =>
      cases index with
      | zero =>
          cases x <;>
            simp [nativeTermTail, nativeSourceBit, ih, Bool.and_assoc,
              Bool.and_comm, Bool.and_left_comm]
      | succ index =>
          simp [nativeTermTail, nativeSourceBit, nativeOutputBit, ih,
            Bool.and_assoc, Bool.and_comm] <;>
            ac_rfl

/-- Incremental Boolean phase split: base parity and mixed internal-bit parity. -/
def nativePhaseStep {n : ℕ} (boundary : Fin n → Bool)
    (state : Bool × Bool) (term : List Nat) : Bool × Bool :=
  let tail := nativeTermTail boundary term
  if term.contains 0 then
    (state.1, state.2 ^^ tail)
  else
    (state.1 ^^ tail, state.2)

/-- The phase split preserves every intermediate XOR accumulator. -/
private theorem nativePhaseStep_sound {n : ℕ}
    (boundary : Fin n → Bool) (term : List Nat)
    (x base mixed : Bool) :
    ((base ^^ (x && mixed)) ^^ term.all (nativeSourceBit x boundary)) =
      ((nativePhaseStep boundary (base, mixed) term).1 ^^
        (x && (nativePhaseStep boundary (base, mixed) term).2)) := by
  rw [nativeTerm_split]
  cases base <;> cases mixed <;> cases x <;>
    cases ht : nativeTermTail boundary term <;>
    cases hz : term.contains 0 <;>
    simp only [nativePhaseStep, ht, hz] <;>
    decide

private theorem nativePhase_split_acc {n : ℕ}
    (boundary : Fin n → Bool) (terms : List (List Nat))
    (x base mixed : Bool) :
    terms.foldl
      (fun parity term => parity ^^ term.all (nativeSourceBit x boundary))
      (base ^^ (x && mixed)) =
      (let state := terms.foldl (nativePhaseStep boundary) (base, mixed)
       state.1 ^^ (x && state.2)) := by
  induction terms generalizing base mixed with
  | nil => rfl
  | cons term rest ih =>
      simp only [List.foldl_cons]
      rw [nativePhaseStep_sound boundary term x base mixed]
      exact ih (nativePhaseStep boundary (base, mixed) term).1
        (nativePhaseStep boundary (base, mixed) term).2

/-- Source-derived quadratic phases split exactly at the internal bit,
for every exterior setting, with no separate source-phase hypothesis.

The mixed part is affine when nativeSourceShape accepts a quadratic source;
the present identity holds even without that restriction. -/
theorem nativePhase_split {n : ℕ}
    (boundary : Fin n → Bool) (terms : List (List Nat)) (x : Bool) :
    nativePhase (nativeSourceBit x boundary) terms =
      (let state := terms.foldl (nativePhaseStep boundary) (false, false)
       state.1 ^^ (x && state.2)) := by
  simpa [nativePhase] using
    nativePhase_split_acc boundary terms x false false

/-- The signed sum is computed directly from the raw source phase,
without separately assuming the polynomial split is correct. For a free
internal bit, a nonzero mixed phase cancels both signed contributions. -/
theorem nativePhase_signed_fiber {n : ℕ}
    (boundary : Fin n → Bool) (terms : List (List Nat)) :
    (∑ x : Bool, signedBit (nativePhase (nativeSourceBit x boundary) terms)) =
      (let state := terms.foldl (nativePhaseStep boundary) (false, false)
       if state.2 = true then 0 else 2 * signedBit state.1) := by
  simp_rw [nativePhase_split]
  exact signedBoolFiber
    (terms.foldl (nativePhaseStep boundary) (false, false)).1
    (terms.foldl (nativePhaseStep boundary) (false, false)).2

/-- Check every raw affine parity constraint against the given coordinate interpreter. -/
def nativeRowsHold (bits : Nat → Bool)
    (rows : List (List Nat × Bool)) : Bool :=
  rows.all (fun row => nativeXorRow bits row.1 == row.2)

/-- Evaluate the source as an integer sign with affine support and multiplicity. -/
def nativeSignedSource {n : ℕ} (src : NativeSourceRecord)
    (x : Bool) (boundary : Fin n → Bool) : ℤ :=
  let bits := nativeSourceBit x boundary
  if nativeRowsHold bits src.rows then
    (2 : ℤ) ^ src.exponent * signedBit (nativePhase bits src.phaseTerms)
  else 0

/-- Evaluate the projected output, including its optional new affine constraint. -/
def nativeSignedOutput {n : ℕ} (out : NativeOutputRecord)
    (boundary : Fin n → Bool) : ℤ :=
  let bits := nativeOutputBit boundary
  let rows := out.rows ++ out.added.toList
  if nativeRowsHold bits rows then
    (2 : ℤ) ^ out.exponent * signedBit (nativePhase bits out.phaseTerms)
  else 0

/-- All shape checks use explicit Boolean folds so they compute under decide. -/
def nativeTermWellFormed (width : ℕ) (term : List Nat) : Bool :=
  decide (term.length ≤ 2) &&
    (term.zip (term.drop 1)).all (fun p => decide (p.1 < p.2)) &&
    term.all (fun i => decide (i < width))

/-- Require degree-two squarefree source monomials and in-range affine row indices. -/
def nativeSourceShape (n : ℕ) (src : NativeSourceRecord) : Bool :=
  src.phaseTerms.all (nativeTermWellFormed (n + 1)) &&
    src.rows.all (fun row => row.1.all (fun i => decide (i < n + 1)))

/-- Require in-range projected terms and rows and a well-formed coefficient receipt. -/
def nativeOutputShape (n : ℕ) (out : NativeOutputRecord) : Bool :=
  out.phaseTerms.all (nativeTermWellFormed n) &&
    out.rows.all (fun row => row.1.all (fun i => decide (i < n))) &&
    out.added.toList.all (fun row => row.1.all (fun i => decide (i < n))) &&
    out.receipt.checkShape n

/-- The finite set of boundary coordinates assigned true. -/
def nativeSupport {n : ℕ} (boundary : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => boundary i = true)

/-- The source-independent check also tests that the signed phase receipt
actually agrees with the output's raw monomial interpreter. -/
def nativeReceiptMatches {n : ℕ} (out : NativeOutputRecord) :
    Prop :=
  ∀ boundary : Fin n → Bool,
    nativePhase (nativeOutputBit boundary) out.phaseTerms =
      phaseBit (out.receipt.decode n) (nativeSupport boundary)

/-- Constructively enumerate the 2^n Boolean vectors in index order.
There is no noncomputable Finset.toList in this executable oracle. -/
def nativeBitVectors : (n : ℕ) → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (nativeBitVectors n).map (false :: ·) ++
        (nativeBitVectors n).map (true :: ·)

theorem nativeBitVectors_complete (n : ℕ) (bits : List Bool)
    (h : bits.length = n) : bits ∈ nativeBitVectors n := by
  induction n generalizing bits with
  | zero =>
      cases bits with
      | nil => simp [nativeBitVectors]
      | cons bit rest => simp at h
  | succ n ih =>
      cases bits with
      | nil => simp at h
      | cons bit rest =>
          have hrest : rest.length = n := by simpa using h
          have ht := ih rest hrest
          cases bit <;> simp [nativeBitVectors, ht]

/-- Read a validated n-bit vector as a native coordinate assignment. -/
def nativeBoundaryFromList {n : ℕ} (bits : List Bool) : Fin n → Bool :=
  fun i => (bits[i.val]?).getD false

/-- Enumerate all Boolean boundary contexts in an executable list.
This remains exponential; it is only the independent finite-instance oracle. -/
def nativeBoundaries (n : ℕ) : List (Fin n → Bool) :=
  (nativeBitVectors n).map nativeBoundaryFromList

/-- For one explicit boundary, independently check the claimed output's
phase record and the exact signed sum over the internal Boolean bit. -/
def nativeBoundaryCheck {n : ℕ}
    (src : NativeSourceRecord) (out : NativeOutputRecord)
    (boundary : Fin n → Bool) : Bool :=
  decide (nativePhase (nativeOutputBit boundary) out.phaseTerms =
    phaseBit (out.receipt.decode n) (nativeSupport boundary)) &&
  decide (nativeSignedOutput out boundary =
    ∑ x : Bool, nativeSignedSource src x boundary)

/-- Executable reference acceptance over raw source and output data.
No native success flag is trusted and no unbounded Prop decision is used. -/
def checkNativeInstance {n : ℕ}
    (src : NativeSourceRecord) (out : NativeOutputRecord) : Bool :=
  nativeSourceShape n src && nativeOutputShape n out &&
    (nativeBoundaries n).all (nativeBoundaryCheck src out)

/-- Every context is included in the finite executable oracle. -/
theorem nativeBoundary_mem {n : ℕ} (boundary : Fin n → Bool) :
    boundary ∈ nativeBoundaries n := by
  apply List.mem_map.mpr
  refine ⟨List.ofFn boundary, ?_, ?_⟩
  · apply nativeBitVectors_complete
    simp
  · funext i
    simp [nativeBoundaryFromList]

theorem checkNativeInstance_boundary {n : ℕ}
    (src : NativeSourceRecord) (out : NativeOutputRecord)
    (accepted : checkNativeInstance (n := n) src out = true)
    (boundary : Fin n → Bool) :
    nativeBoundaryCheck src out boundary = true := by
  have h := accepted
  simp only [checkNativeInstance, Bool.and_eq_true] at h
  have hall := h.2
  simp only [List.all_eq_true] at hall
  exact hall boundary (nativeBoundary_mem boundary)

/-- Exhaustive instance acceptance implies exact source-to-output signed projection. -/
theorem checkNativeInstance_sound {n : ℕ}
    (src : NativeSourceRecord) (out : NativeOutputRecord)
    (accepted : checkNativeInstance (n := n) src out = true)
    (boundary : Fin n → Bool) :
    nativeSignedOutput out boundary =
      ∑ x : Bool, nativeSignedSource src x boundary := by
  have h := checkNativeInstance_boundary src out accepted boundary
  simp only [nativeBoundaryCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- Exhaustive acceptance also validates the output coefficient receipt. -/
theorem checkNativeInstance_receipt_sound {n : ℕ}
    (src : NativeSourceRecord) (out : NativeOutputRecord)
    (accepted : checkNativeInstance (n := n) src out = true)
    (boundary : Fin n → Bool) :
    nativePhase (nativeOutputBit boundary) out.phaseTerms =
      phaseBit (out.receipt.decode n) (nativeSupport boundary) := by
  have h := checkNativeInstance_boundary src out accepted boundary
  simp only [nativeBoundaryCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

private def freeOracleSource : NativeSourceRecord :=
  { phaseTerms := [[0, 1]], rows := [], exponent := 0 }

private def freeOracleOutput : NativeOutputRecord :=
  { phaseTerms := [], rows := [],
    added := some ([0], false), exponent := 1,
    receipt := { constant := false, linear := [false], orderedPairs := [] } }

/-- Summing (-1)^(x*b) leaves the affine constraint b = 0. -/
example : checkNativeInstance (n := 1)
    freeOracleSource freeOracleOutput = true := by decide

private def forcedOracleSource : NativeSourceRecord :=
  { phaseTerms := [[0, 1]], rows := [([0, 1], true)], exponent := 0 }

private def forcedOracleOutput : NativeOutputRecord :=
  { phaseTerms := [], rows := [], added := none, exponent := 0,
    receipt := { constant := false, linear := [false], orderedPairs := [] } }

/-- x XOR b = 1 forces x = !b; consequently x*b is always zero. -/
example : checkNativeInstance (n := 1)
    forcedOracleSource forcedOracleOutput = true := by decide

/-- A forged exponent must be rejected. -/
example : checkNativeInstance (n := 1) freeOracleSource
    { freeOracleOutput with exponent := 0 } = false := by decide

#print axioms IndependentETH.QuadraticLowWeight.canonicalTerm_value
#print axioms IndependentETH.QuadraticLowWeight.toggleCanonical_value
#print axioms IndependentETH.QuadraticLowWeight.canonicalization_value
#print axioms IndependentETH.QuadraticLowWeight.nativeConstructorOK_sound
#print axioms IndependentETH.QuadraticLowWeight.nativeConstruct_sound
#print axioms IndependentETH.QuadraticLowWeight.nativeConstruct_refuses

#print axioms IndependentETH.QuadraticLowWeight.nativeTerm_split
#print axioms IndependentETH.QuadraticLowWeight.nativePhase_split
#print axioms IndependentETH.QuadraticLowWeight.nativePhase_signed_fiber

#print axioms IndependentETH.QuadraticLowWeight.checkNativeInstance_sound
#print axioms IndependentETH.QuadraticLowWeight.checkNativeInstance_receipt_sound

#print axioms IndependentETH.QuadraticLowWeight.SparseCoefficientRecord.decode_eval
#print axioms IndependentETH.QuadraticLowWeight.checkSparseSamples_sign_sound
#print axioms IndependentETH.QuadraticLowWeight.xorFold_eq_zmod_sum

#print axioms IndependentETH.QuadraticLowWeight.checkSamples_sound
#print axioms IndependentETH.QuadraticLowWeight.checkSamples_complete
#print axioms IndependentETH.QuadraticLowWeight.checkSamples_sign_sound
#print axioms IndependentETH.QuadraticLowWeight.checkedFreeLocalExact
#print axioms IndependentETH.QuadraticLowWeight.checkedForcedLocalExact

#print axioms IndependentETH.QuadraticLowWeight.eval_pair
#print axioms IndependentETH.QuadraticLowWeight.linear_from_samples
#print axioms IndependentETH.QuadraticLowWeight.pair_from_samples
#print axioms IndependentETH.QuadraticLowWeight.ext_of_low_weight_samples

end IndependentETH.QuadraticLowWeight
