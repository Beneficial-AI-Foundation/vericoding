/-
  Port of vericoding_dafnybench_0058_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : index1 < arr.size)
  (h_1 : index2 < arr[index1]!.Length)
  (h_2 : ∀ i: nat, j:nat :: i < arr.size ∧ j < arr.size ∧ i ≠ j → arr[i]! ≠ arr[j]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks