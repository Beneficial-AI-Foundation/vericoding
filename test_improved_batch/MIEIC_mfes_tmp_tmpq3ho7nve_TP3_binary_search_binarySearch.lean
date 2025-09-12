/-
  Port of MIEIC_mfes_tmp_tmpq3ho7nve_TP3_binary_search_binarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def binarySearch (a : Array Int) (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem binarySearch_spec (a : Array Int) (x : Int) (index : Int) :=
  (h_0 : isSorted(a))
  : -1 ≤ index < a.size ∧ if index ≠ -1 then a[index]! == x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks