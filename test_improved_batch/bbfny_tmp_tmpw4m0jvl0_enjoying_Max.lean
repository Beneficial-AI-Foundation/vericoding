/-
  Port of bbfny_tmp_tmpw4m0jvl0_enjoying_Max.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def max (a : Int) (b : Int) : Int :=
  if a > b then a else b

def abs (x : Int) : Int :=
  if x < 0 then -x else x

def fib (n : Nat) : Nat :=
  sorry  -- TODO: implement complex function body

def Max (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (a : Int) (b : Int) (c : Int) :=
  : a ≤ c ∧ b ≤ c ∧ a == c ∨ b == c
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks