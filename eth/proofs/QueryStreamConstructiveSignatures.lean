import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

/-!
# Executable first-occurrence subtree semantics for QueryStream

The pinned original `SignatureTupleTraversal.subtreeTotal` is a
`noncomputable def` because it sums over a subtype of first-occurrence
representatives under a classical finite instance. This file makes that
particular mathematical traversal constructive when the original signature
keys have decidable equality.

It preserves *all* source events: each candidate test (including duplicates),
each exhaustion, and each completed attained tuple. It does not enumerate
#SAT assignments or replace the two-pass numerical leaf visitor.

Source pin: openai/math@4eaee87548250b2682affda7d05d947c05554bae,
  SqrtLogSpace/SignatureTupleTraversal.lean,
  SqrtLogSpace/AttainedSignatures.lean.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamConstructiveSignatures

open scoped BigOperators
open SignatureTupleDFS
open SignatureTupleTraversal

variable {N : ℕ → ℕ} {κ : ℕ → Type*}
variable [∀ d, DecidableEq (κ d)]

/-- Constructive first-occurrence decision. The source's actual
    `AttainedSignatures.duplicateScan` is a bounded Boolean predecessor
    scan whose `rescan_emits_iff` theorem establishes this same predicate. -/
def fresh (key : (d : ℕ) → Fin (N d) → κ d)
    (depth : ℕ) (i : Fin (N depth)) : Bool :=
  decide (∀ j : Fin (N depth), j < i → key depth j ≠ key depth i)

@[simp] theorem fresh_eq_true_iff
    (key : (d : ℕ) → Fin (N d) → κ d)
    (depth : ℕ) (i : Fin (N depth)) :
    fresh key depth i = true ↔
      ∀ j : Fin (N depth), j < i → key depth j ≠ key depth i := by
  simp [fresh]

/-- Every first-occurrence signature contributes exactly once, in numerical
    candidate order, without constructing a subtype `Finset.univ` at runtime.
    This is a constructive public counterpart of the original module's
    private mathematical `sum_representatives` lemma. -/
def scanSum {M : Type*} [AddCommMonoid M]
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    (f : Representatives key depth → M) : M :=
  ∑ i : Fin (N depth),
    if h : ∀ j : Fin (N depth), j < i → key depth j ≠ key depth i then
      f ⟨i, h⟩ else 0

theorem scanSum_eq_representatives {M : Type*} [AddCommMonoid M]
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    (f : Representatives key depth → M) :
    scanSum key depth f = ∑ rep : Representatives key depth, f rep := by
  classical
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    split_ifs with h
    · exact (hi ⟨⟨i, h⟩, rfl⟩).elim
    · rfl
  · intro i
    rw [dite_eq_left i.property]

/-- Explicit finite source-ordered traversal of the *same* event tree as the
    noncomputable original: the first sum counts every tested candidate, the
    second charges exhaustion, and the third recursively descends only for
    first-occurrence keys. Recursion decreases `remaining`; no subtype
    enumeration, materialized tuple family, or unbounded search is used. -/
def subtreeTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M]
    (weight : SignatureTupleTraversal.Event key levels → M) :
    (remaining depth : ℕ) → depth + remaining = levels →
      Prefix (Representatives key) depth → M := by
  intro remaining
  induction remaining with
  | zero =>
      intro depth h ancestors
      have he : depth = levels := by omega
      exact weight (.leaf (he ▸ ancestors))
  | succ remaining ih =>
      intro depth h ancestors
      let d : Fin levels := ⟨depth, by omega⟩
      exact (∑ i : Fin (N depth), weight (.candidate d ancestors i)) +
        weight (.exhausted d ancestors) +
        ∑ i : Fin (N depth),
          if hrep : ∀ j : Fin (N depth), j < i → key depth j ≠ key depth i then
            ih (depth + 1) (by omega) (Fin.snoc ancestors ⟨i, hrep⟩)
          else 0

/-- Universal equality at every subtree boundary, not only at the final
    numerical answer. In particular it holds for weights charging rejected
    candidates and generator exhaustion, as well as for leaf sums. -/
theorem subtreeTotal_eq_original (key : (d : ℕ) → Fin (N d) → κ d)
    (levels : ℕ) {M : Type*} [AddCommMonoid M]
    (weight : SignatureTupleTraversal.Event key levels → M)
    (remaining depth : ℕ) (h : depth + remaining = levels)
    (ancestors : Prefix (Representatives key) depth) :
    subtreeTotal key levels weight remaining depth h ancestors =
      SignatureTupleTraversal.subtreeTotal key levels weight remaining depth h ancestors := by
  induction remaining generalizing depth with
  | zero =>
      have he : depth = levels := by omega
      subst depth
      rfl
  | succ remaining ih =>
      let d : Fin levels := ⟨depth, by omega⟩
      simp only [← Nat.succ_eq_add_one]
      dsimp [subtreeTotal, SignatureTupleTraversal.subtreeTotal, Nat.recAux]
      congr 1
      classical
      rw [← scanSum_eq_representatives key depth
        (fun rep : Representatives key depth =>
          SignatureTupleTraversal.subtreeTotal key levels weight remaining
            (depth + 1) (by omega) (Fin.snoc ancestors rep))]
      unfold scanSum
      apply Finset.sum_congr rfl
      intro i _
      by_cases hrep : ∀ j : Fin (N depth), j < i → key depth j ≠ key depth i
      · simp only [dif_pos hrep]
        exact ih (depth + 1) (by omega) (Fin.snoc ancestors ⟨i, hrep⟩)
      · simp only [dif_neg hrep]

/-- The numerical source DFS begins with an empty attained prefix. -/
def runTotal (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M]
    (weight : SignatureTupleTraversal.Event key levels → M) : M :=
  subtreeTotal key levels weight levels 0 (by omega) (fun i => Fin.elim0 i)

theorem runTotal_eq_original
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M]
    (weight : SignatureTupleTraversal.Event key levels → M) :
    runTotal key levels weight =
      SignatureTupleTraversal.subtreeTotal key levels weight levels 0 (by omega)
        (fun i => Fin.elim0 i) :=
  subtreeTotal_eq_original key levels weight levels 0 (by omega)
    (fun i => Fin.elim0 i)

/-- All candidates, including duplicates, and every exhausted generator cost
    one. Each completed attained tuple also costs one. -/
def unitEventWeight {key : (d : ℕ) → Fin (N d) → κ d} {levels : ℕ} :
    SignatureTupleTraversal.Event key levels → ℕ := fun _ => 1

def exampleKey (_depth : ℕ) (i : Fin 4) : ℕ := i.val % 2

example : runTotal exampleKey 0 (unitEventWeight) = 1 := by decide
example : runTotal exampleKey 1 (unitEventWeight) = 7 := by decide
example : runTotal exampleKey 2 (unitEventWeight) = 19 := by decide

#eval runTotal exampleKey 0 unitEventWeight
#eval runTotal exampleKey 1 unitEventWeight
#eval runTotal exampleKey 2 unitEventWeight

#print axioms scanSum_eq_representatives
#print axioms subtreeTotal_eq_original
#print axioms runTotal_eq_original

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamConstructiveSignatures
