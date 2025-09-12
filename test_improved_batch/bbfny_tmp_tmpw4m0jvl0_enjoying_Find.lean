/-
  Port of bbfny_tmp_tmpw4m0jvl0_enjoying_Find.dfy
  
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

def Find (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Find_spec (a : Array Int) (key : Int) (index : Int) :=
  : 0 ≤ index → index < a.size ∧ a[index]! == key ∧ index < 0 → ∀ k :: 0 ≤ k < a.size → a[k]! ≠ key
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks