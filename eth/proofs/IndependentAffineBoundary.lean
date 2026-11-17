import Mathlib

/-!
# Compact exact affine interface: a two-row parity CNF family

An affine region with internal Boolean bits u,v and boundary bits b,c
has equations u xor v = b and u xor v = c. Exactly two internal pairs
satisfy both equations when b=c, and none otherwise.

This is a *universal finite theorem*, not a test or a source-to-Rust proof.
It justifies the particular two-equation affine interface's semantic
formula. General GF(2) rank-nullity elimination and implementation
correspondence remain separate obligations.
-/

namespace IndependentETH.AffineBoundary

open scoped BigOperators

/-- A full, unexpanded sum over all *internal* Boolean assignments. -/
def direct (b c : Bool) : ℕ :=
  ∑ u : Bool, ∑ v : Bool,
    if Bool.xor u v = b ∧ Bool.xor u v = c then 1 else 0

/-- The exact compact boundary interface for two equal-left parity rows. -/
def compact (b c : Bool) : ℕ :=
  if b = c then 2 else 0

/-- The elimination identity holds for *every* external Boolean boundary. -/
theorem direct_eq_compact (b c : Bool) :
    direct b c = compact b c := by
  cases b <;> cases c <;> decide

/-- Any weighted outer continuation preserves the elimination identity. -/
theorem weighted_context (b c : Bool) (weight : ℤ) :
    weight * (direct b c : ℤ) = weight * (compact b c : ℤ) := by
  rw [direct_eq_compact]

/-- Composition of two regions with distinct outgoing boundary constraints
    is exact under every external assignment. -/
theorem product_context (b c d : Bool) :
    direct b c * direct b d = compact b c * compact b d := by
  rw [direct_eq_compact, direct_eq_compact]

/-- The two-region interface must *not* be identified at arbitrary
    boundaries merely because it agrees at one observed assignment. -/
theorem distinct_context_counterexample :
    direct false true ≠ direct false false := by
  decide


/-- Canonical four-clause representation of x XOR y XOR z = 0.
    The four clauses exclude the odd-parity assignments. -/
def xor3CNF (x y z : Bool) : Bool :=
  (x || y || !z) &&
  (x || !y || z) &&
  (!x || y || z) &&
  (!x || !y || !z)

/-- Truth-functional proof of the CNF-to-affine source recognition rule. -/
theorem xor3CNF_iff_even (x y z : Bool) :
    xor3CNF x y z = true ↔ Bool.xor (Bool.xor x y) z = false := by
  cases x <;> cases y <;> cases z <;> decide

/-- The first source CNF block is equivalent to u xor v = b. -/
theorem xor3CNF_iff_boundary (u v b : Bool) :
    xor3CNF u v b = true ↔ Bool.xor u v = b := by
  cases u <;> cases v <;> cases b <;> decide

/-- Two canonical CNF XOR blocks satisfy the same exact internal-count
    interface. This ties the clause encoding theorem to finite counting. -/
theorem two_cnf_blocks_count (b c : Bool) :
    (∑ u : Bool, ∑ v : Bool,
      if xor3CNF u v b && xor3CNF u v c then (1 : ℕ) else 0)
    = compact b c := by
  cases b <;> cases c <;> decide

#print axioms IndependentETH.AffineBoundary.xor3CNF_iff_even
#print axioms IndependentETH.AffineBoundary.xor3CNF_iff_boundary
#print axioms IndependentETH.AffineBoundary.two_cnf_blocks_count

#print axioms IndependentETH.AffineBoundary.direct_eq_compact
#print axioms IndependentETH.AffineBoundary.weighted_context
#print axioms IndependentETH.AffineBoundary.product_context
#print axioms IndependentETH.AffineBoundary.distinct_context_counterexample
