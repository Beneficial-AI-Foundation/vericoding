/-
  Port of vericoding_dafnybench_0206_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (a : Int) (b : Int) : Int :=
  if a < b then a else b

def minMethod (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem minMethod_spec (a : Int) (b : Int) (c : Int) :=
  : c ≤ a ∧ c ≤ b ∧ c == a ∨ c == b
  := by
  sorry  -- TODO: implement proof

def minArray (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem minArray_spec (a : Array Int) (m : Int) :=
  (h_0 : a≠ null  ∧ a.size > 0 ;)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks