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

-- Source-recursive finite sums require a larger elaboration budget, not more
-- runtime fuel or a weaker theorem.
set_option maxHeartbeats 2000000

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
      let f : Representatives key depth → M := fun rep =>
        subtreeTotal key levels weight remaining (depth + 1) (by omega)
          (Fin.snoc ancestors rep)
      have hscan :
          (∑ i : Fin (N depth),
            if hrep : ∀ j : Fin (N depth), j < i → key depth j ≠ key depth i then
              subtreeTotal key levels weight remaining (depth + 1) (by omega)
                (Fin.snoc ancestors ⟨i, hrep⟩)
            else 0) =
          ∑ rep : Representatives key depth, f rep := by
        exact scanSum_eq_representatives key depth f
      calc
        _ = ∑ rep : Representatives key depth, f rep := hscan
        _ = _ := by
          apply Finset.sum_congr
          · ext rep
            simp
          · intro rep _
            exact ih (depth + 1) (by omega) (Fin.snoc ancestors rep)

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

/-!
## Recover the source's event total

The original source has a **private** \`sum_subtreeTotal\` theorem and an
exported \`eventTotal_callbackWeight\` theorem. The adapter below exposes
only the equality needed for our new executable root, keeping the
source's event weights and its representatives unchanged.
-/

/-- Reindex a full level of attained prefixes using the source's exact
\`Fin.snocEquiv\`. No signature tuple is chosen by this proof. -/
private theorem sum_snoc_for_source
    (key : (d : ℕ) → Fin (N d) → κ d) (depth : ℕ)
    {M : Type*} [AddCommMonoid M]
    (f : Prefix (Representatives key) (depth + 1) → M) :
    (∑ ancestors : Prefix (Representatives key) depth,
      ∑ rep : Representatives key depth, f (Fin.snoc ancestors rep)) =
      ∑ ancestors, f ancestors := by
  classical
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact (Fin.snocEquiv (fun i : Fin (depth + 1) => Representatives key i.val)).sum_comp f

/-- A public bridge to the mathematical identity hidden in the unchanged
original's private \`sum_subtreeTotal\` lemma. It sums complete source
subtrees at a depth, **including** rejected candidates and exhaustion.
Only the already-verified source recurrence is unfolded. -/
theorem source_subtree_sum
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M]
    (weight : SignatureTupleTraversal.Event key levels → M)
    (remaining depth : ℕ) (h : depth + remaining = levels) :
    (∑ ancestors : Prefix (Representatives key) depth,
      SignatureTupleTraversal.subtreeTotal key levels weight remaining depth h ancestors) =
        (∑ d ∈ Finset.Ico depth levels,
          SignatureTupleTraversal.levelTotal key levels weight d) +
          ∑ ancestors : Prefix (Representatives key) levels,
            weight (.leaf ancestors) := by
  classical
  induction remaining generalizing depth with
  | zero =>
      have he : depth = levels := by omega
      subst depth
      simp [SignatureTupleTraversal.subtreeTotal]
  | succ remaining ih =>
      have hd : depth < levels := by omega
      simp only [← Nat.succ_eq_add_one]
      change (∑ ancestors : Prefix (Representatives key) depth,
        (((∑ i : Fin (N depth), weight (.candidate ⟨depth, hd⟩ ancestors i)) +
          weight (.exhausted ⟨depth, hd⟩ ancestors)) +
        ∑ rep : Representatives key depth,
          SignatureTupleTraversal.subtreeTotal key levels weight remaining
            (depth + 1) (by omega) (Fin.snoc ancestors rep))) = _
      rw [Finset.sum_add_distrib, sum_snoc_for_source, ih (depth + 1) (by omega),
        Finset.sum_eq_sum_Ico_succ_bot hd]
      simp only [SignatureTupleTraversal.levelTotal, dite_eq_left hd]
      simp only [add_assoc]

/-- Fully general source-event bridge. \`runTotal\` is a total function of
the decidable keys and concrete event weights, whereas \`eventTotal\` is
the original mathematical noncomputable sum. Their results agree exactly. -/
theorem runTotal_eq_eventTotal
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M]
    (weight : SignatureTupleTraversal.Event key levels → M) :
    runTotal key levels weight =
      SignatureTupleTraversal.eventTotal key levels weight := by
  rw [runTotal_eq_original]
  have hs := source_subtree_sum key levels weight levels 0 (by omega)
  rw [Fintype.sum_subsingleton _ (fun i => Fin.elim0 i)] at hs
  calc
    _ = (∑ i ∈ Finset.range levels,
          SignatureTupleTraversal.levelTotal key levels weight i) +
        ∑ ancestors : Prefix (Representatives key) levels,
          weight (.leaf ancestors) := by
      simpa only [← Finset.range_eq_Ico] using hs
    _ = SignatureTupleTraversal.eventTotal key levels weight := by
      unfold SignatureTupleTraversal.eventTotal
      apply congrArg (fun x : M =>
        (∑ i ∈ Finset.range levels,
          SignatureTupleTraversal.levelTotal key levels weight i) + x)
      apply Finset.sum_congr
      · ext a
        simp
      · intro a _
        rfl

/-- The constructive complete DFS returns **exactly the original
attained-tuple leaf sum** when candidate and exhaustion weights vanish.
This lemma only replaces the proof-side signature enumeration, not the
actual numerical \`emittedValue\` computation. -/
theorem runTotal_callbackWeight
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M]
    (value : Prefix (Representatives key) levels → M) :
    runTotal key levels
      (SignatureTupleTraversal.callbackWeight key levels value) =
        ∑ ancestors : Prefix (Representatives key) levels, value ancestors := by
  rw [runTotal_eq_eventTotal]
  refine (SignatureTupleTraversal.eventTotal_callbackWeight key levels value).trans ?_
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    rfl

#print axioms runTotal_eq_eventTotal
#print axioms runTotal_callbackWeight

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
