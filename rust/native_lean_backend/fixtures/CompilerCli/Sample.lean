namespace Sample

def inc (x : UInt64) : UInt64 := x + 1

def twice (x : UInt64) : UInt64 := inc (inc x)

def choose (x y : UInt64) : UInt64 :=
  if x < y then twice x else inc y

end Sample

#guard Sample.inc 41 == 42
#guard Sample.twice 40 == 42
#guard Sample.choose 3 10 == 5
