import Mathlib

/-!
# Exact staged contraction for overlapping factor scopes

A factor may depend on several shared Boolean variables. We express its
declared scope as a finite set of variable names and require a locality
certificate: changing a variable outside that scope does not change the
factor's value.

The theorem covers any number of such factors, arbitrary overlapping
declared scopes, arbitrary processing order, and arbitrary commutative
semiring weights. Each elimination list must be safe for every *future*
factor. No small-width or runtime claim is made.

The native Rust GF(2) representation is NOT refined by this proof.
-/

namespace IndependentETH.OverlappingFactors

open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- A Boolean value for every globally named variable. -/
abbrev Assignment (V : Type*) := V → Bool
/-- A semiring-valued function on complete Boolean assignments. -/
abbrev Weight (V R : Type*) := Assignment V → R

/-- Pointwise multiplication of functions on the same global assignment. -/
def times (f g : Weight V R) : Weight V R :=
  fun x => f x * g x

/-- Pointwise multiplication inherits associativity from the semiring. -/
theorem times_assoc (f g h : Weight V R) :
    times (times f g) h = times f (times g h) := by
  funext x
  exact mul_assoc (f x) (g x) (h x)

/-- Sum over the two values of one Boolean variable, retaining all others. -/
def eliminateAt (v : V) (f : Weight V R) : Weight V R :=
  fun x => f (Function.update x v false) +
    f (Function.update x v true)

/-- Eliminate a list of Boolean variables, in the explicit given order. -/
def eliminateList (xs : List V) (f : Weight V R) : Weight V R :=
  xs.foldl (fun acc v => eliminateAt v acc) f

/-- Consecutive elimination lists compose in their stated order. -/
theorem eliminateList_append (xs ys : List V) (f : Weight V R) :
    eliminateList (xs ++ ys) f =
      eliminateList ys (eliminateList xs f) := by
  simp only [eliminateList, List.foldl_append]

/-- Pull a factor past one exact sum only when it ignores the summed bit. -/
theorem eliminateAt_mul_of_invariant
    (v : V) (f g : Weight V R)
    (h : ∀ x b, g (Function.update x v b) = g x) :
    times (eliminateAt v f) g =
      eliminateAt v (times f g) := by
  funext x
  change
    (f (Function.update x v false) +
      f (Function.update x v true)) * g x =
    f (Function.update x v false) *
      g (Function.update x v false) +
    f (Function.update x v true) *
      g (Function.update x v true)
  rw [h x false, h x true, add_mul]

/-- Pull a future factor past an arbitrary sequence of previously
eliminated variables, provided it ignores every one of them. -/
theorem eliminateList_mul_of_invariant
    (xs : List V) (f g : Weight V R)
    (h : ∀ v ∈ xs, ∀ x b, g (Function.update x v b) = g x) :
    times (eliminateList xs f) g =
      eliminateList xs (times f g) := by
  induction xs generalizing f with
  | nil => rfl
  | cons v vs ih =>
      have hv : ∀ x b, g (Function.update x v b) = g x := by
        intro x b
        exact h v (by simp) x b
      have hvs : ∀ w ∈ vs, ∀ x b,
          g (Function.update x w b) = g x := by
        intro w hw x b
        exact h w (by simp [hw]) x b
      change
        times (eliminateList vs (eliminateAt v f)) g =
        eliminateList vs (eliminateAt v (times f g))
      rw [ih (eliminateAt v f) hvs]
      rw [eliminateAt_mul_of_invariant v f g hv]

/-- A scope certificate: every variable omitted from the declared scope
is semantically irrelevant to the factor, for every full assignment. -/
structure ScopedFactor (V R : Type*) [DecidableEq V] where
  scope : Finset V
  value : Weight V R
  local_update : ∀ v, v ∉ scope →
    ∀ x b, value (Function.update x v b) = value x

/-- One factor and exactly the variables newly eliminated after accepting it.
A legal plan must not use those variables in later factors. -/
structure Step (V R : Type*) [DecidableEq V] where
  factor : ScopedFactor V R
  dead : List V

/-- Concatenate the variables removed by each contraction stage. -/
def eliminated : List (Step V R) → List V
  | [] => []
  | s :: rest => s.dead ++ eliminated rest

/-- Product of arbitrary overlapping-scope factors. Shared variables
are *one global variable*, not cloned per factor. -/
def factorProduct : List (Step V R) → Weight V R
  | [] => fun _ => 1
  | s :: rest => times s.factor.value (factorProduct rest)

/-- Staged execution of the abstract exact operator. This definition
is specification-level and does not implement Rust Gaussian elimination. -/
def contract (acc : Weight V R) : List (Step V R) → Weight V R
  | [] => acc
  | s :: rest =>
      contract (eliminateList s.dead (times acc s.factor.value)) rest

/-- Semantic safety: no future factor may depend on any variable that
the earlier stages have already eliminated. -/
def Safe (hidden : List V) : List (Step V R) → Prop
  | [] => True
  | s :: rest =>
      (∀ v ∈ hidden, v ∉ s.factor.scope) ∧
      Safe (hidden ++ s.dead) rest

/-- Union of the declared supports of the factors still unprocessed. -/
def scopeUnion : List (ScopedFactor V R) → Finset V
  | [] => ∅
  | f :: rest => f.scope ∪ scopeUnion rest

/-- Actual liveness construction: keep exactly ports needed by the
remaining source scopes or by the requested external output. -/
def nextKept (active : Finset V) (f : ScopedFactor V R)
    (rest : List (ScopedFactor V R)) (output : Finset V) :
    Finset V :=
  (active ∪ f.scope) ∩ (scopeUnion rest ∪ output)

/-- Newly dead ports, converted to a mathematical elimination list.
A finite set has no canonical list order without an explicit ordering;
this reference conversion is noncomputable, unlike Rust's BTreeSet. -/
noncomputable def nextDead (active : Finset V) (f : ScopedFactor V R)
    (rest : List (ScopedFactor V R)) (output : Finset V) :
    List V :=
  ((active ∪ f.scope) \ (scopeUnion rest ∪ output)).toList

/-- A complete order-respecting plan, with a terminal identity factor
that explicitly closes any active ports not requested as output.
This matters when the source factor list is empty. Source factors may share ports
with preceding and following factors; only actual future dependencies
prevent elimination. -/
noncomputable def makePlan (active output : Finset V) :
    List (ScopedFactor V R) → List (Step V R)
  | [] =>
      [{ factor := {
           scope := ∅,
           value := fun _ => 1,
           local_update := by intros; rfl
         },
         dead := (active \ output).toList }]
  | f :: rest =>
      { factor := f, dead := nextDead active f rest output } ::
      makePlan (nextKept active f rest output) output rest

/-- The set-based liveness constructor implies the semantic safety
premise required for exact contraction: no already hidden variable
ever appears in a future declared factor scope. -/
theorem makePlan_safe
    (active output : Finset V) (factors : List (ScopedFactor V R)) :
    ∀ (hidden : List V),
      (∀ v ∈ hidden, v ∉ scopeUnion factors) →
      Safe hidden (makePlan active output factors) := by
  induction factors generalizing active with
  | nil =>
      intro hidden _
      change (∀ v ∈ hidden, v ∉ (∅ : Finset V)) ∧ True
      constructor
      · intro v hv
        simp
      · trivial
  | cons f rest ih =>
      intro hidden hhidden
      change (∀ v ∈ hidden, v ∉ f.scope) ∧
        Safe (hidden ++ nextDead active f rest output)
          (makePlan (nextKept active f rest output) output rest)
      constructor
      · intro v hv
        have hh := hhidden v hv
        simp only [scopeUnion, Finset.mem_union, not_or] at hh
        exact hh.1
      · apply ih
        intro v hv
        rcases List.mem_append.mp hv with hold | hnew
        · have hh := hhidden v hold
          simp only [scopeUnion, Finset.mem_union, not_or] at hh
          exact hh.2
        · have hh : v ∈ (active ∪ f.scope) \
              (scopeUnion rest ∪ output) := by
            simpa only [nextDead, Finset.mem_toList] using hnew
          have hnot : v ∉ scopeUnion rest ∪ output :=
            (Finset.mem_sdiff.mp hh).2
          simp only [Finset.mem_union, not_or] at hnot
          exact hnot.1

/-- General overlap theorem: arbitrary scopes may share any variables
that remain live. The recursive staged contraction equals the direct
product of ALL factors followed by exactly the recorded eliminations.

The theorem is symbolic and uniform in the initial accumulator, all
assignments, the number/order of factors, and the coefficient semiring.
An external plan must additionally ensure each dead variable is summed
once and that every variable intended to be hidden is eventually removed. -/
theorem contract_correct (steps : List (Step V R)) :
    ∀ (hidden : List V) (base : Weight V R),
      Safe hidden steps →
      contract (eliminateList hidden base) steps =
        eliminateList (hidden ++ eliminated steps)
          (times base (factorProduct steps)) := by
  induction steps with
  | nil =>
      intro hidden base _
      change eliminateList hidden base =
        eliminateList (hidden ++ [])
          (times base (fun _ => 1))
      simp only [List.append_nil]
      congr 1
      funext x
      simp only [times, mul_one]
  | cons s rest ih =>
      intro hidden base hsafe
      obtain ⟨hscope, hrest⟩ := hsafe
      have hlocal : ∀ v ∈ hidden, ∀ x b,
          s.factor.value (Function.update x v b) =
          s.factor.value x := by
        intro v hv x b
        exact s.factor.local_update v (hscope v hv) x b
      calc
        contract (eliminateList hidden base) (s :: rest) =
            contract
              (eliminateList s.dead
                (times (eliminateList hidden base) s.factor.value))
              rest := rfl
        _ = contract
              (eliminateList (hidden ++ s.dead)
                (times base s.factor.value)) rest := by
              rw [eliminateList_mul_of_invariant hidden base s.factor.value hlocal]
              rw [eliminateList_append]
        _ = eliminateList ((hidden ++ s.dead) ++ eliminated rest)
              (times (times base s.factor.value)
                (factorProduct rest)) :=
              ih (hidden ++ s.dead) (times base s.factor.value) hrest
        _ = eliminateList (hidden ++ eliminated (s :: rest))
              (times base (factorProduct (s :: rest))) := by
              simp only [eliminated, factorProduct,
                List.append_assoc, times_assoc]

/-- An ordinary uncompressed starting function satisfies the same result,
with no initially eliminated variables. -/
theorem contract_from_raw
    (steps : List (Step V R)) (base : Weight V R)
    (hsafe : Safe [] steps) :
    contract base steps =
      eliminateList (eliminated steps)
        (times base (factorProduct steps)) := by
  simpa [eliminateList] using
    (contract_correct steps [] base hsafe)

#print axioms IndependentETH.OverlappingFactors.eliminateAt_mul_of_invariant
#print axioms IndependentETH.OverlappingFactors.eliminateList_mul_of_invariant
#print axioms IndependentETH.OverlappingFactors.contract_correct
#print axioms IndependentETH.OverlappingFactors.contract_from_raw

/-- The Rust-style future-scope planner automatically meets the safety
precondition of the general overlapping-factor contraction theorem. -/
theorem generated_plan_correct
    (active output : Finset V)
    (factors : List (ScopedFactor V R)) (base : Weight V R) :
    contract base (makePlan active output factors) =
      eliminateList (eliminated (makePlan active output factors))
        (times base (factorProduct (makePlan active output factors))) := by
  apply contract_from_raw
  apply makePlan_safe
  intro v hv
  cases hv

#print axioms IndependentETH.OverlappingFactors.makePlan_safe
#print axioms IndependentETH.OverlappingFactors.generated_plan_correct

/-! ## Exactly-once elimination and the declared-variable universe

The generated plan's prior safety theorem did not establish that
the elimination list contains each intended source variable precisely once.
The following results distinguish the source-declared universe from variables
actually mentioned in any factor scope. In particular, a never-mentioned
Boolean variable must contribute a factor two to a *closed* model count.
-/

/-- At any point, the generated plan eventually eliminates exactly the
active or future-scope variables not requested as external output. -/
theorem makePlan_mem_iff
    (active output : Finset V) (factors : List (ScopedFactor V R))
    (v : V) :
    v ∈ eliminated (makePlan active output factors) ↔
      v ∈ (active ∪ scopeUnion factors) \ output := by
  induction factors generalizing active with
  | nil =>
      simp [makePlan, eliminated, scopeUnion, Finset.mem_sdiff]
  | cons f rest ih =>
      simp only [makePlan, eliminated, List.mem_append, scopeUnion]
      rw [ih (nextKept active f rest output)]
      simp only [nextDead, Finset.mem_toList,
        Finset.mem_sdiff, nextKept, Finset.mem_inter,
        Finset.mem_union]
      tauto

/-- No variable is ever summed twice by the generated live-scope plan. -/
theorem makePlan_nodup
    (active output : Finset V) (factors : List (ScopedFactor V R)) :
    (eliminated (makePlan active output factors)).Nodup := by
  induction factors generalizing active with
  | nil =>
      simpa [makePlan, eliminated] using
        (Finset.nodup_toList (active \ output))
  | cons f rest ih =>
      change
        (nextDead active f rest output ++
          eliminated (makePlan
            (nextKept active f rest output) output rest)).Nodup
      apply List.Nodup.append
      · exact Finset.nodup_toList _
      · exact ih (nextKept active f rest output)
      · intro v hdead hlater
        have hnew : v ∈ (active ∪ f.scope) \
            (scopeUnion rest ∪ output) := by
          simpa only [nextDead, Finset.mem_toList] using hdead
        have hremain :
            v ∈ (nextKept active f rest output ∪ scopeUnion rest) \
              output :=
          (makePlan_mem_iff
            (nextKept active f rest output) output rest v).mp hlater
        simp only [Finset.mem_sdiff, Finset.mem_union,
          Finset.mem_inter, nextKept] at *
        tauto

/-- Source-declared variables invisible to every factor must still be
counted unless explicitly retained as external outputs. -/
noncomputable def unusedDeclared (declared output : Finset V)
    (factors : List (ScopedFactor V R)) : List V :=
  (declared \ (scopeUnion factors ∪ output)).toList

/-- The complete closed-source elimination list includes both
unused declared variables and all factor-associated hidden variables. -/
noncomputable def allSourceEliminated
    (declared output : Finset V)
    (factors : List (ScopedFactor V R)) : List V :=
  unusedDeclared declared output factors ++
    eliminated (makePlan ∅ output factors)

/-- The complete elimination list includes precisely the declared
non-output variable names, including names absent from all factors. -/
theorem allSourceEliminated_mem_iff
    (declared output : Finset V)
    (factors : List (ScopedFactor V R))
    (hscopes : scopeUnion factors ⊆ declared)
    (v : V) :
    v ∈ allSourceEliminated declared output factors ↔
      v ∈ declared \ output := by
  simp only [allSourceEliminated, List.mem_append]
  rw [makePlan_mem_iff]
  simp only [unusedDeclared, Finset.mem_toList,
    Finset.mem_sdiff, Finset.mem_union]
  have hs : v ∈ scopeUnion factors → v ∈ declared :=
    fun hv => hscopes hv
  tauto

/-- All eliminated source variables are unique, not merely members
of the correct set. Therefore each declared, non-output Boolean
variable is summed *exactly once*. -/
theorem allSourceEliminated_nodup
    (declared output : Finset V)
    (factors : List (ScopedFactor V R)) :
    (allSourceEliminated declared output factors).Nodup := by
  change
    (unusedDeclared declared output factors ++
      eliminated (makePlan ∅ output factors)).Nodup
  apply List.Nodup.append
  · exact Finset.nodup_toList _
  · exact makePlan_nodup ∅ output factors
  · intro v hunused hplan
    have hu : v ∈ declared \ (scopeUnion factors ∪ output) := by
      simpa only [unusedDeclared, Finset.mem_toList] using hunused
    have hp : v ∈ (∅ ∪ scopeUnion factors) \ output :=
      (makePlan_mem_iff ∅ output factors v).mp hplan
    simp only [Finset.mem_sdiff, Finset.mem_union] at *
    simp at hp
    tauto

/-- The generated plan also remains safe when the source universe has
extra, unused variables already eliminated from the starting unit weight. -/
theorem declared_plan_correct
    (declared output : Finset V)
    (factors : List (ScopedFactor V R))
    (base : Weight V R) :
    contract
      (eliminateList (unusedDeclared declared output factors) base)
      (makePlan ∅ output factors) =
    eliminateList (allSourceEliminated declared output factors)
      (times base (factorProduct (makePlan ∅ output factors))) := by
  apply contract_correct
  apply makePlan_safe
  intro v hv
  have hu : v ∈ declared \ (scopeUnion factors ∪ output) := by
    simpa only [unusedDeclared, Finset.mem_toList] using hv
  have hn := (Finset.mem_sdiff.mp hu).2
  simp only [Finset.mem_union, not_or] at hn
  exact hn.1

#print axioms IndependentETH.OverlappingFactors.makePlan_mem_iff
#print axioms IndependentETH.OverlappingFactors.makePlan_nodup
#print axioms IndependentETH.OverlappingFactors.allSourceEliminated_mem_iff
#print axioms IndependentETH.OverlappingFactors.allSourceEliminated_nodup
#print axioms IndependentETH.OverlappingFactors.declared_plan_correct


/-! ## Deterministic sorted plans for executable correspondence

The preceding set-to-list operation is intentionally noncomputable over
an unordered variable type. With a declared linear order, Finset.sort
supplies a concrete list. These theorems prove that choosing this sorted
order preserves semantic safety, exactly-once coverage, and contraction
correctness. They do not prove Rust's BTreeSet implementation refines
Lean's sorting algorithm or that the packed GF(2) kernel refines the
abstract contraction operator.
-/

section OrderedPlan

variable [LinearOrder V]

/-- Explicitly ordered, computable replacement for Finset.toList. -/
def sortedDead (active : Finset V) (f : ScopedFactor V R)
    (rest : List (ScopedFactor V R)) (output : Finset V) : List V :=
  ((active ∪ f.scope) \ (scopeUnion rest ∪ output)).sort (· ≤ ·)

/-- Every stage, including the terminal neutral stage, uses sorted
rather than arbitrarily chosen elimination order. -/
def sortedPlan (active output : Finset V) :
    List (ScopedFactor V R) → List (Step V R)
  | [] =>
      [{ factor := {
           scope := ∅,
           value := fun _ => 1,
           local_update := by intros; rfl
         },
         dead := (active \ output).sort (· ≤ ·) }]
  | f :: rest =>
      { factor := f, dead := sortedDead active f rest output } ::
        sortedPlan (nextKept active f rest output) output rest

/-- A generated ordered plan never drops a variable that a future
factor could observe. The ordering decision is irrelevant to safety. -/
theorem sortedPlan_safe
    (active output : Finset V) (factors : List (ScopedFactor V R)) :
    ∀ hidden : List V,
      (∀ v ∈ hidden, v ∉ scopeUnion factors) →
      Safe hidden (sortedPlan active output factors) := by
  induction factors generalizing active with
  | nil =>
      intro hidden _
      change (∀ v ∈ hidden, v ∉ (∅ : Finset V)) ∧ True
      constructor
      · intro v hv
        simp
      · trivial
  | cons f rest ih =>
      intro hidden hhidden
      change (∀ v ∈ hidden, v ∉ f.scope) ∧
        Safe (hidden ++ sortedDead active f rest output)
          (sortedPlan (nextKept active f rest output) output rest)
      constructor
      · intro v hv
        have hh := hhidden v hv
        simp only [scopeUnion, Finset.mem_union, not_or] at hh
        exact hh.1
      · apply ih
        intro v hv
        rcases List.mem_append.mp hv with hold | hnew
        · have hh := hhidden v hold
          simp only [scopeUnion, Finset.mem_union, not_or] at hh
          exact hh.2
        · have hh : v ∈ (active ∪ f.scope) \
              (scopeUnion rest ∪ output) := by
            simpa only [sortedDead, Finset.mem_sort] using hnew
          have hnot := (Finset.mem_sdiff.mp hh).2
          simp only [Finset.mem_union, not_or] at hnot
          exact hnot.1

/-- The ordered plan eliminates exactly the currently active or
future-used variables that the output does not require. -/
theorem sortedPlan_mem_iff
    (active output : Finset V) (factors : List (ScopedFactor V R))
    (v : V) :
    v ∈ eliminated (sortedPlan active output factors) ↔
      v ∈ (active ∪ scopeUnion factors) \ output := by
  induction factors generalizing active with
  | nil =>
      simp [sortedPlan, eliminated, scopeUnion, Finset.mem_sdiff]
  | cons f rest ih =>
      simp only [sortedPlan, eliminated, List.mem_append, scopeUnion]
      rw [ih (nextKept active f rest output)]
      simp only [sortedDead, Finset.mem_sort,
        Finset.mem_sdiff, nextKept, Finset.mem_inter,
        Finset.mem_union]
      tauto

/-- The concrete ordered plan does not sum any variable twice. -/
theorem sortedPlan_nodup
    (active output : Finset V) (factors : List (ScopedFactor V R)) :
    (eliminated (sortedPlan active output factors)).Nodup := by
  induction factors generalizing active with
  | nil =>
      simpa [sortedPlan, eliminated] using
        (Finset.sort_nodup (active \ output) (· ≤ ·))
  | cons f rest ih =>
      change
        (sortedDead active f rest output ++
          eliminated (sortedPlan
            (nextKept active f rest output) output rest)).Nodup
      apply List.Nodup.append
      · exact Finset.sort_nodup _ (· ≤ ·)
      · exact ih (nextKept active f rest output)
      · intro v hdead hlater
        have hnew : v ∈ (active ∪ f.scope) \
            (scopeUnion rest ∪ output) := by
          simpa only [sortedDead, Finset.mem_sort] using hdead
        have hremain :
            v ∈ (nextKept active f rest output ∪ scopeUnion rest) \
              output :=
          (sortedPlan_mem_iff
            (nextKept active f rest output) output rest v).mp hlater
        simp only [Finset.mem_sdiff, Finset.mem_union,
          Finset.mem_inter, nextKept] at *
        tauto

/-- Explicitly sorted invisible-source variables. -/
def sortedUnusedDeclared (declared output : Finset V)
    (factors : List (ScopedFactor V R)) : List V :=
  (declared \ (scopeUnion factors ∪ output)).sort (· ≤ ·)

/-- The ordered plan includes unused declared variables before staged elimination. -/
def sortedSourceEliminated (declared output : Finset V)
    (factors : List (ScopedFactor V R)) : List V :=
  sortedUnusedDeclared declared output factors ++
    eliminated (sortedPlan ∅ output factors)

/-- Each declared non-output variable occurs in the ordered list. -/
theorem sortedSourceEliminated_mem_iff
    (declared output : Finset V)
    (factors : List (ScopedFactor V R))
    (hscopes : scopeUnion factors ⊆ declared)
    (v : V) :
    v ∈ sortedSourceEliminated declared output factors ↔
      v ∈ declared \ output := by
  simp only [sortedSourceEliminated, List.mem_append]
  rw [sortedPlan_mem_iff]
  simp only [sortedUnusedDeclared, Finset.mem_sort,
    Finset.mem_sdiff, Finset.mem_union]
  have hs : v ∈ scopeUnion factors → v ∈ declared :=
    fun hv => hscopes hv
  tauto

/-- Each declared non-output variable occurs at most once. -/
theorem sortedSourceEliminated_nodup
    (declared output : Finset V)
    (factors : List (ScopedFactor V R)) :
    (sortedSourceEliminated declared output factors).Nodup := by
  change
    (sortedUnusedDeclared declared output factors ++
      eliminated (sortedPlan ∅ output factors)).Nodup
  apply List.Nodup.append
  · exact Finset.sort_nodup _ (· ≤ ·)
  · exact sortedPlan_nodup ∅ output factors
  · intro v hunused hplan
    have hu : v ∈ declared \ (scopeUnion factors ∪ output) := by
      simpa only [sortedUnusedDeclared, Finset.mem_sort] using hunused
    have hp : v ∈ (∅ ∪ scopeUnion factors) \ output :=
      (sortedPlan_mem_iff ∅ output factors v).mp hplan
    simp only [Finset.mem_sdiff, Finset.mem_union] at *
    simp at hp
    tauto

/-- The ordered plan calculates the exact original product followed by
the generated sorted elimination list, with no semantic approximation. -/
theorem sortedSource_correct
    (declared output : Finset V)
    (factors : List (ScopedFactor V R))
    (base : Weight V R) :
    contract
      (eliminateList (sortedUnusedDeclared declared output factors) base)
      (sortedPlan ∅ output factors) =
    eliminateList (sortedSourceEliminated declared output factors)
      (times base (factorProduct (sortedPlan ∅ output factors))) := by
  apply contract_correct
  apply sortedPlan_safe
  intro v hv
  have hu : v ∈ declared \ (scopeUnion factors ∪ output) := by
    simpa only [sortedUnusedDeclared, Finset.mem_sort] using hv
  have hn := (Finset.mem_sdiff.mp hu).2
  simp only [Finset.mem_union, not_or] at hn
  exact hn.1

/-- The ordered representation has no duplicate entries even for an
arbitrary finite source inventory, independently of its representation. -/
example (source : Finset ℕ) :
    (source.sort (· ≤ ·)).Nodup :=
  Finset.sort_nodup source (· ≤ ·)

end OrderedPlan

#print axioms IndependentETH.OverlappingFactors.sortedPlan_safe
#print axioms IndependentETH.OverlappingFactors.sortedPlan_mem_iff
#print axioms IndependentETH.OverlappingFactors.sortedPlan_nodup
#print axioms IndependentETH.OverlappingFactors.sortedSourceEliminated_mem_iff
#print axioms IndependentETH.OverlappingFactors.sortedSourceEliminated_nodup
#print axioms IndependentETH.OverlappingFactors.sortedSource_correct
