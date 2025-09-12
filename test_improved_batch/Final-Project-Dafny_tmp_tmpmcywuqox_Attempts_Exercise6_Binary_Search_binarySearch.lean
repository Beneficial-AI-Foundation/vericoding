/-
  Port of Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise6_Binary_Search_binarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def binarySearch (a : Array Int) (val : Int) : Int :=
  sorry  -- TODO: implement function body

theorem binarySearch_spec (a : Array Int) (val : Int) (pos : Int) :=
  (h_0 : a.size > 0)
  (h_1 : ∀ i, j :: 0 ≤ i < j < a.size → a[i]! ≤ a[j]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks