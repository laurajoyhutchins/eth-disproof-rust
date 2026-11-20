import Mathlib

/-!
# Exact live-port fold and independent-private factor induction

The set-theoretic statements model the Rust left fold's ordered scopes.
The source program intentionally starts with an *unprojected* first leaf:
after the first merge its port set is the live set, and the induction
then preserves this fact for any remaining order.

The separate semiring-valued factor induction handles arbitrarily many
independent private blocks conditioned on a common exterior assignment.
It does not yet formalize arbitrary overlapping variable-dependent
factor graphs or prove the Rust bit-vector executor refines these semantics.
-/

namespace IndependentETH.LivePortFold

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- Union of the explicitly declared port sets in an ordered factor suffix. -/
def scopeUnion : List (Finset V) → Finset V
  | [] => ∅
  | h :: t => h ∪ scopeUnion t

/-- The observable interface after processing `seen` when `future`
    is still waiting and `output` must remain externally observable. -/
def livePorts (seen future output : Finset V) : Finset V :=
  seen ∩ (future ∪ output)

/-- After absorbing the next factor, a staged contraction can drop precisely
    the currently exposed ports not referenced by the future or output. -/
def nextPorts (current next future output : Finset V) : Finset V :=
  (current ∪ next) ∩ (future ∪ output)

/-- Exact set equality used by the Rust `kept` construction. -/
theorem nextPorts_eq_livePorts (seen next future output : Finset V) :
    nextPorts (livePorts seen (next ∪ future) output)
      next future output =
    livePorts (seen ∪ next) future output := by
  ext v
  simp only [nextPorts, livePorts, Finset.mem_inter, Finset.mem_union]
  tauto

/-- If a port was eliminated from the old prefix then it can never
    legitimately reappear in the next factor, future, or output. -/
theorem dead_port_not_needed
    (seen next future output : Finset V) (v : V)
    (hseen : v ∈ seen)
    (hdead : v ∉ livePorts seen (next ∪ future) output) :
    v ∉ next ∧ v ∉ future ∧ v ∉ output := by
  simp only [livePorts, Finset.mem_inter, Finset.mem_union] at hdead
  simp only [not_and] at hdead
  have h := hdead hseen
  tauto

/-- The pure set computation of all future merge steps. It is deliberately
    independent of any GF(2) equations or multiplicity arithmetic. -/
def runPorts (current : Finset V) (order : List (Finset V))
    (output : Finset V) : Finset V :=
  match order with
  | [] => current
  | next :: future =>
      runPorts (nextPorts current next (scopeUnion future) output)
        future output

/-- Induction over an arbitrary suffix of ordered factor port sets.
    If the initial interface is live, every later interface is live. -/
theorem runPorts_correct
    (seen : Finset V) (order : List (Finset V)) (output : Finset V) :
    runPorts (livePorts seen (scopeUnion order) output) order output =
      livePorts (seen ∪ scopeUnion order) ∅ output := by
  induction order generalizing seen with
  | nil =>
      simp [runPorts, scopeUnion, livePorts]
  | cons next future ih =>
      change
        runPorts
          (nextPorts (livePorts seen (next ∪ scopeUnion future) output)
            next (scopeUnion future) output) future output =
        livePorts (seen ∪ (next ∪ scopeUnion future)) ∅ output
      rw [nextPorts_eq_livePorts]
      rw [ih (seen ∪ next)]
      simp only [Finset.union_assoc]

/-- The Rust fold starts with the unprojected first leaf, not a normalized
    live interface. The first merge removes any already dead first-leaf ports.
    Thus the same end-to-end liveness theorem holds for every nonempty tail. -/
theorem runPorts_from_raw_first
    (first next : Finset V) (rest : List (Finset V))
    (output : Finset V) :
    runPorts first (next :: rest) output =
      livePorts (first ∪ next ∪ scopeUnion rest) ∅ output := by
  change
    runPorts
      (nextPorts first next (scopeUnion rest) output) rest output =
    livePorts (first ∪ next ∪ scopeUnion rest) ∅ output
  change
    runPorts
      (livePorts (first ∪ next) (scopeUnion rest) output)
        rest output =
    livePorts (first ∪ next ∪ scopeUnion rest) ∅ output
  exact runPorts_correct (first ∪ next) rest output

section IndependentPrivateBlocks

variable {I A P R : Type*} [Fintype A] [CommSemiring R]

/-- A nested exact sum over private assignments of the remaining factors,
    with the shared exterior assignment held fixed. -/
def direct (factor : I → A → P → R) : List I → P → R
  | [], _ => 1
  | i :: rest, p => ∑ a : A, factor i a p * direct factor rest p

/-- Eliminate each independent private assignment before multiplying.
    No factor depends on another factor's private variable. -/
def compact (factor : I → A → P → R) : List I → P → R
  | [], _ => 1
  | i :: rest, p => (∑ a : A, factor i a p) * compact factor rest p

/-- Exact arbitrary-length induction, valid for every ordered list of
    factors and every shared boundary assignment. -/
theorem independent_private_fold_correct
    (factor : I → A → P → R) (factors : List I) (p : P) :
    compact factor factors p = direct factor factors p := by
  induction factors with
  | nil => rfl
  | cons i rest ih =>
      change (∑ a : A, factor i a p) * compact factor rest p =
        ∑ a : A, factor i a p * direct factor rest p
      rw [ih, Finset.sum_mul]

/-- The compact result is a commutative product of exact local fibers. -/
theorem compact_eq_product
    (factor : I → A → P → R) (factors : List I) (p : P) :
    compact factor factors p =
      (factors.map (fun i => ∑ a : A, factor i a p)).prod := by
  induction factors with
  | nil => rfl
  | cons i rest ih =>
      simp only [compact, List.map_cons, List.prod_cons]
      rw [ih]

/-- Any two permutations of the same independent private blocks have
    the same exact exterior function, not just the same closed total. -/
theorem compact_perm
    (factor : I → A → P → R) {xs ys : List I}
    (h : xs.Perm ys) (p : P) :
    compact factor xs p = compact factor ys p := by
  rw [compact_eq_product, compact_eq_product]
  exact (h.map (fun i => ∑ a : A, factor i a p)).prod_eq

/-- Direct nested enumeration is also invariant under factor permutation. -/
theorem direct_perm
    (factor : I → A → P → R) {xs ys : List I}
    (h : xs.Perm ys) (p : P) :
    direct factor xs p = direct factor ys p := by
  calc
    direct factor xs p = compact factor xs p :=
      (independent_private_fold_correct factor xs p).symm
    _ = compact factor ys p := compact_perm factor h p
    _ = direct factor ys p := independent_private_fold_correct factor ys p

end IndependentPrivateBlocks

#print axioms IndependentETH.LivePortFold.nextPorts_eq_livePorts
#print axioms IndependentETH.LivePortFold.dead_port_not_needed
#print axioms IndependentETH.LivePortFold.runPorts_correct
#print axioms IndependentETH.LivePortFold.runPorts_from_raw_first
#print axioms IndependentETH.LivePortFold.independent_private_fold_correct
#print axioms IndependentETH.LivePortFold.compact_eq_product
#print axioms IndependentETH.LivePortFold.compact_perm
#print axioms IndependentETH.LivePortFold.direct_perm
