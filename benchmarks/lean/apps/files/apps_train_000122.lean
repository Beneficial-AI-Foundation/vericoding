/-
Suppose an array sorted in ascending order is rotated at some pivot unknown to you beforehand.

(i.e., [0,0,1,2,2,5,6] might become [2,5,6,0,0,1,2]).

You are given a target value to search. If found in the array return true, otherwise return false.

Example 1:

Input: nums = [2,5,6,0,0,1,2], target = 0
Output: true

Example 2:

Input: nums = [2,5,6,0,0,1,2], target = 3
Output: false

Follow up:

       This is a follow up problem to Search in Rotated Sorted Array, where nums may contain duplicates.
       Would this affect the run-time complexity? How and why?
-/

-- <vc-helpers>
-- </vc-helpers>

def search (list : List Int) (target : Int) : Bool := sorry

theorem search_target_in_list_returns_true (nums : List Int) (target : Int) : 
  search (nums ++ [target]) target = true := sorry

theorem search_target_not_in_list_returns_false (nums : List Int) (target : Int) :
  (¬ target ∈ nums) → search nums target = false := sorry

theorem search_matches_contains (nums : List Int) (target : Int) :
  search nums target = (target ∈ nums) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval search [2, 5, 6, 0, 0, 1, 2] 0

/-
info: False
-/
-- #guard_msgs in
-- #eval search [2, 5, 6, 0, 0, 1, 2] 3

/-
info: True
-/
-- #guard_msgs in
-- #eval search [1] 1

-- Apps difficulty: interview
-- Assurance level: unguarded