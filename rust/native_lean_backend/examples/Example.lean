import NativeRust

namespace Example

def addOne (x : UInt64) : UInt64 := x + 1
def timesThree (x : UInt64) : UInt64 := x * 3
def subtractSeven (x : UInt64) : UInt64 := x - 7
def twoArgs (x y : UInt64) : UInt64 := x + y

def multi (x : UInt64) : UInt64 := (x + 5) * 3

#guard addOne 41 == 42
#guard timesThree 7 == 21
#guard subtractSeven 3 == (3 - 7 : UInt64)
#guard twoArgs 2 3 == 5
#guard multi 7 == 36

end Example

#native_rust Example.addOne as "add_one" to "examples/generated_add_one.rs"
#native_rust Example.timesThree as "times_three" to "examples/generated_times_three.rs"
#native_rust Example.subtractSeven as "subtract_seven" to "examples/generated_subtract_seven.rs"
#native_rust Example.twoArgs as "two_args" to "examples/generated_two_args.rs"
#native_rust Example.multi as "multi" to "examples/generated_multi.rs"
