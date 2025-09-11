-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: 3
-/
-- #guard_msgs in
-- #eval findSubarraySum [1, 3, -4, 2, 2, -2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval findSubarraySum [0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval findSubarraySum [1, -1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded