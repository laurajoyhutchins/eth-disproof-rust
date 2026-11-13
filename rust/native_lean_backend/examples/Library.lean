namespace Library
  def bump (x : UInt64) : UInt64 := x + 1
  def triple (x : UInt64) : UInt64 := x * 3
  def left (x : UInt64) : UInt64 := triple (bump x)
  def right (x : UInt64) : UInt64 := bump (bump x)
end Library
