/-
  Port of vericoding_dafnybench_0527_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SplitArray (arr : Array Int) (L : Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem SplitArray_spec (arr : Array Int) (L : Int) (firstPart : seq<int>) :=
  (h_0 : 0 ≤ L ≤ arr.size)
  : |firstPart| == L ∧ |secondPart| == arr.size - L ∧ firstPart + secondPart == arr[..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks