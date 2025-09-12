/-
  Port of vericoding_dafnybench_0372_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def remove_duplicates_from_sorted_array (nums : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem remove_duplicates_from_sorted_array_spec (nums : seq<int>) (result : seq<int>) :=
  (h_0 : is_sorted(nums))
  (h_1 : 1 ≤ |nums| ≤ 30000)
  (h_2 : ∀ i :: 0 ≤ i < |nums| → -100 ≤ nums[i]! ≤ 100)
  : is_sorted_and_distinct(result) ∧ ∀ i :: i in nums <→ i in result
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks