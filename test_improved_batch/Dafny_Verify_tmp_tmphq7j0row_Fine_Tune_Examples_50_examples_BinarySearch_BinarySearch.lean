/-
  Port of Dafny_Verify_tmp_tmphq7j0row_Fine_Tune_Examples_50_examples_BinarySearch_BinarySearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BinarySearch (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (key : Int) (n : Int) :=
  (h_0 : ∀ i, j :: 0 ≤ i < j < a.size → a[i]! ≤ a[j]!)
  : 0 ≤ n ≤ a.size ∧ ∀ i :: 0 ≤ i < n → a[i]! < key ∧ ∀ i :: n ≤ i < a.size → key ≤ a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks