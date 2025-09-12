/-
  Port of bbfny_tmp_tmpw4m0jvl0_enjoying_Abs.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (a : Int) (b : Int) : Int :=
  if a > b then a else b

def abs (x : Int) : Int :=
  if x < 0 then -x else x

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body


  := by
  sorry  -- TODO: implement proof

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : y == abs(x)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks