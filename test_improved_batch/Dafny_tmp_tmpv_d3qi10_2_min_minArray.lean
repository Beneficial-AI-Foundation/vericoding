/-
  Port of Dafny_tmp_tmpv_d3qi10_2_min_minArray.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (a : Int) (b : Int) : Int :=
  if a < b then a else b

def minArray (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem minArray_spec (a : Array Int) (m : Int) :=
  (h_0 : a≠ null  ∧ a.size > 0 ;)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks