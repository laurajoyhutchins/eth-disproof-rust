/-
The declarations in this module are compiled by the original Lean compiler.
The Reader emission checker reads their actual Lean.IR.Decl, not their syntax.
-/
namespace ScalarFixture

def plus (x y : UInt64) : UInt64 := x + y
-- Reader supports subtraction, but the proved model does not.
-- Certification must reject this declaration even if general codegen succeeds.
def subtract (x y : UInt64) : UInt64 := x - y

def choose (x y : UInt64) : UInt64 :=
  if x < y then x + 1 else y * 3
def nested (x y : UInt64) : UInt64 :=
  if x == y then x * 3
  else if x <= y then x + y
  else y * 7

#guard plus 17 25 == 42
#guard choose 2 5 == 3
#guard choose 5 2 == 6
#guard nested 4 4 == 12
#guard nested 3 5 == 8
#guard nested 7 2 == 14

end ScalarFixture
