/-
  Port of vericoding_dafnybench_0240_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def twoSum (nums : Array Int) (target : Int) : Int :=
  sorry  -- TODO: implement function body

theorem twoSum_spec (nums : Array Int) (target : Int) (index1 : Int) :=
  (h_0 : 2 ≤ nums.size)
  (h_1 : ∃ i, j :: (0 ≤ i < j < nums.size ∧ nums[i]! + nums[j]! == target))
  : index1 ≠ index2 ∧ 0 ≤ index1 < nums.size ∧ 0 ≤ index2 < nums.size ∧ nums[index1]! + nums[index2]! == target
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks