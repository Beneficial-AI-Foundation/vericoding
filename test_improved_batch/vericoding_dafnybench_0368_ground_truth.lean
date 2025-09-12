/-
  Port of vericoding_dafnybench_0368_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def contains_duplicate (nums : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem contains_duplicate_spec (nums : seq<int>) (result : Bool) :=
  (h_0 : 1 ≤ |nums| ≤ 100000)
  (h_1 : ∀ i :: 0 ≤ i < |nums| → -1000000000 ≤ nums[i]! ≤ 1000000000)
  : result <→ distinct(nums)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks