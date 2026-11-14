import NativeRust

namespace Item30Errors

def unsupportedNatBitwise (x y : Nat) : Nat := Nat.land x y
def unsupportedStringPush (s : String) : String := s.push '!'
def unsupportedArrayPop (a : Array UInt64) : UInt64 :=
  (a.pop).getD 0 0

end Item30Errors

#native_rust Item30Errors.unsupportedNatBitwise as "bad_nat_bitwise" to "examples/sem_rejected_nat_bitwise.rs"
#native_rust Item30Errors.unsupportedStringPush as "bad_string_push" to "examples/sem_rejected_string_push.rs"
#native_rust Item30Errors.unsupportedArrayPop as "bad_array_get" to "examples/sem_rejected_array_pop.rs"
