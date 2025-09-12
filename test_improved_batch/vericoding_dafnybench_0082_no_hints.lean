/-
  Port of vericoding_dafnybench_0082_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def twoSum (nums : Array Int) (target : Int) : Int :=
  sorry  -- TODO: implement function body

theorem twoSum_spec (nums : Array Int) (target : Int) (i : Int) :=
  (h_0 : nums.size > 1)
  (h_1 : ∃ i,j::0 ≤ i < j < nums.size ∧  nums[i]! + nums[j]! == target)
  : 0 ≤ i < j < nums.size ∧ nums[i]! + nums[j]! == target ∧ ∀ ii jj, (0 ≤ ii < i ∧ ii < jj < nums.size)  → nums[ii]! + nums[jj]! ≠ target ∧ ∀ jj:: i < jj < j → nums[i]! + nums[jj]! ≠ target
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks