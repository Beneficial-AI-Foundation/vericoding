/-
  Port of vericoding_dafnybench_0497_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def KthElement (arr : Array Int) (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem KthElement_spec (arr : Array Int) (k : Int) (result : Int) :=
  (h_0 : 1 ≤ k ≤ arr.size)
  : result == arr[k - 1]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks