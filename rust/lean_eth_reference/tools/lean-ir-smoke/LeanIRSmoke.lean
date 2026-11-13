namespace LeanIRSmoke

def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = n + n := by
  rfl

end LeanIRSmoke
