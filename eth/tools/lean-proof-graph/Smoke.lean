import Lean
namespace ProofGraphSmoke
 def double (n : Nat) : Nat := n + n
 theorem twice (n : Nat) : double n = n + n := rfl
end ProofGraphSmoke
