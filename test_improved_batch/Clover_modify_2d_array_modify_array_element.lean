/-
  Port of Clover_modify_2d_array_modify_array_element.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : index1 < arr.size)
  (h_1 : index2 < arr[index1]!.Length)
  (h_2 : ∀ i: nat, j:nat :: i < arr.size ∧ j < arr.size ∧ i ≠ j → arr[i]! ≠ arr[j]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks