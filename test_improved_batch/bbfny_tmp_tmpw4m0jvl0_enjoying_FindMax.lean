/-
  Port of bbfny_tmp_tmpw4m0jvl0_enjoying_FindMax.dfy
  
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

def FindMax (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindMax_spec (a : Array Int) (i : Int) :=
  (h_0 : a.size ≥ 1)
  : 0 ≤ i < a.size ∧ ∀ k :: 0 ≤ k < a.size → a[k]! ≤ a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks