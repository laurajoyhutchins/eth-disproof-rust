import Mathlib
import ACC.RankedComponentCertificate

/-!
# Indexed ranked-parent certificate, the executable guard boundary

The Rust verifier reads arrays and source-edge indices, not an arbitrary
parent function. This model uses finite vertex/label indices and original
edge-list positions, then decodes a parent using the same orientation rule.
The accepted ranked-guard predicate already checks source-edge membership
for every decoded parent, so a separate decoder-membership lemma is not
required for the exactness theorem.

The new theorem proves that the finite indexed Boolean guard implies
the earlier abstract RankedConditions, hence the exact component quotient
and mathematical contraction. The model excludes malformed usize bounds
by construction; Rust's bounds checks and code-to-model equivalence remain
separate implementation obligations.
-/

namespace ACC.IndexedRankedCertificate

open scoped BigOperators
open ACC.RankedComponentCertificate
open ACC.EqualityEdgeClosure

/-- The Rust parent-index lookup: the first endpoint takes precedence;
    otherwise the second, otherwise the link is invalid. -/
def decodedParent {n : ℕ}
    (edges : List (Fin n × Fin n))
    (sourceIndex : Fin n → Option (Fin edges.length))
    (i : Fin n) : Option (Fin n) :=
  match sourceIndex i with
  | none => none
  | some k =>
    let e := edges.get k
    if e.1 == i then some e.2
    else if e.2 == i then some e.1
    else none

/-- Source-index absence always decodes to absence. -/
theorem decoded_none_of_absent {n : ℕ}
    (edges : List (Fin n × Fin n))
    (sourceIndex : Fin n → Option (Fin edges.length))
    (i : Fin n) (h : sourceIndex i = none) :
    decodedParent edges sourceIndex i = none := by
  simp [decodedParent, h]

/-- This Boolean guard captures source-index validity as an indexed scan,
    followed by the already proved ranked-parent local guards. In particular,
    a nonempty but nonincident source index must never decode as a root. -/
def checkIndexed {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ) : Bool :=
  (List.finRange n).all (fun i =>
    decide ((sourceIndex i).isSome → (decodedParent edges sourceIndex i).isSome)) &&
  checkRanked edges label root (decodedParent edges sourceIndex) rank

/-- A passing indexed Boolean check discharges all the preceding
    mathematical ranked-parent conditions, with no trusted graph oracle. -/
theorem checkIndexed_sound {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (h : checkIndexed edges label root sourceIndex rank = true) :
    RankedConditions edges label root (decodedParent edges sourceIndex) rank := by
  have hrank : checkRanked edges label root
      (decodedParent edges sourceIndex) rank = true := by
    have hh := h
    simp only [checkIndexed, Bool.and_eq_true] at hh
    exact hh.2
  exact checkRanked_sound edges label root
    (decodedParent edges sourceIndex) rank hrank

/-- The extra index guard establishes that any claimed parent reference
    is actually incident to its child, not merely that decoding succeeded. -/
theorem checkIndexed_index_incident {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (h : checkIndexed edges label root sourceIndex rank = true)
    (i : Fin n) (hindex : (sourceIndex i).isSome = true) :
    (decodedParent edges sourceIndex i).isSome = true := by
  have hh := h
  simp only [checkIndexed, Bool.and_eq_true] at hh
  have hscan :
      (List.finRange n).all (fun j =>
        decide ((sourceIndex j).isSome →
          (decodedParent edges sourceIndex j).isSome)) = true := hh.1
  have hi := (List.all_eq_true.mp hscan) i (List.mem_finRange i)
  have himp : (sourceIndex i).isSome = true →
      (decodedParent edges sourceIndex i).isSome = true := by
    simpa only [decide_eq_true_eq] using hi
  exact himp hindex

/-- The indexed Boolean verifier's acceptance implies source-level
    semantic correctness for signed integer equality-component contraction. -/
theorem checked_indexed_contraction {n c : ℕ}
    (edges : List (Fin n × Fin n))
    (label : Fin n → Fin c) (root : Fin c → Fin n)
    (sourceIndex : Fin n → Option (Fin edges.length))
    (rank : Fin n → ℕ)
    (weight : Fin n → Bool → ℤ)
    (h : checkIndexed edges label root sourceIndex rank = true) :
    (∑ x : {x : Fin n → Bool // ∀ e ∈ edges, x e.1 = x e.2},
       ∏ i : Fin n, weight i (x.1 i)) =
    ∏ k : Fin c, ∑ bit : Bool,
      ∏ i ∈ (Finset.univ : Finset (Fin n)) with label i = k,
        weight i bit := by
  exact ranked_contraction edges label root
    (decodedParent edges sourceIndex) rank
    (checkIndexed_sound edges label root sourceIndex rank h) weight

/-- A tiny positive cross-language fixture: vertices 0 and 1 joined,
    vertex 2 isolated. The indexed source link is incident to vertex 1. -/
example :
    checkIndexed (n := 3) (c := 2)
      ([(0, 1)] : List (Fin 3 × Fin 3))
      (fun i => if i = 2 then 1 else 0)
      (fun k => if k = 0 then 0 else 2)
      (fun i => if i = 1 then some (0 : Fin 1) else none)
      (fun i => if i = 1 then 1 else 0) = true := by decide

/-- A nonincident source reference cannot masquerade as an absent parent. -/
example :
    checkIndexed (n := 3) (c := 2)
      ([(0, 1)] : List (Fin 3 × Fin 3))
      (fun i => if i = 2 then 1 else 0)
      (fun k => if k = 0 then 0 else 2)
      (fun i => if i = 2 then some (0 : Fin 1)
        else if i = 1 then some (0 : Fin 1) else none)
      (fun i => if i = 1 then 1 else 0) = false := by decide

#print axioms ACC.IndexedRankedCertificate.checkIndexed_sound
#print axioms ACC.IndexedRankedCertificate.checkIndexed_index_incident
#print axioms ACC.IndexedRankedCertificate.checked_indexed_contraction

end ACC.IndexedRankedCertificate
