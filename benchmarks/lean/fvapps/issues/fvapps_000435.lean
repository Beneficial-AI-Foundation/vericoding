-- <vc-preamble>
def min_difference (nums : List Int) : Int := sorry

theorem min_difference_small_list {nums : List Int} (h : nums.length ≤ 4) : 
  min_difference nums = 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted (nums : List Int) : Bool := sorry

theorem min_difference_sort_invariant {nums : List Int} :
  min_difference nums = min_difference (List.filter (fun x => true) nums) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_difference_nonnegative {nums : List Int} :
  min_difference nums ≥ 0 := sorry

theorem min_difference_bounded {nums : List Int} (h : nums.length > 0) :
  min_difference nums ≤ (nums.maximum? |>.getD 0) - (nums.minimum? |>.getD 0) := sorry

theorem min_difference_large_lists {nums : List Int} (h : nums.length ≥ 5) :
  ∃ d1 d2 d3 d4 : Int, min_difference nums = min d1 (min d2 (min d3 d4)) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_difference [2, 3, 4, 5]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_difference [1, 5, 0, 10, 14]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_difference [6, 6, 0, 1, 1, 4, 6]
-- </vc-theorems>