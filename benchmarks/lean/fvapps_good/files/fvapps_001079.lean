-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findSubarraySum (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_array_has_subarray (arr : List Int) :
  arr = [0] → findSubarraySum arr ≥ 1 :=
  sorry

theorem opposing_pairs_increase_subarrays (arr : List Int) :
  let arr_with_opposites := arr ++ (arr.map (fun x => -x))
  findSubarraySum arr_with_opposites ≥ findSubarraySum arr :=
  sorry

theorem duplicate_array_increases_subarrays (arr : List Int) :
  let doubled := arr ++ arr 
  findSubarraySum doubled ≥ findSubarraySum arr :=
  sorry
-- </vc-theorems>