/-
  Port of vericoding_dafnybench_0209_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def add (x : int32) (y : int32) : int32 :=
  sorry  -- TODO: implement function body

def sub (x : int32) (y : int32) : int32 :=
  sorry  -- TODO: implement function body

def mul (x : int32) (y : int32) : int32 :=
  sorry  -- TODO: implement function body

def div (x : int32) (y : int32) : int32 :=
  if (-2147483648 ≤ (x as Int) / (y as Int) ≤ 2147483647) then x / y else 0

def mod (x : int32) (y : int32) : int32 :=
  x % y /* * Given that y is int32 and * given that the remainder is positive and smaller than the denominator * the result cannot over/underflow and is, therefore, not checked */

function abs(x: int32): (r: int32)
  sorry  -- TODO: implement complex function body

end DafnyBenchmarks