/-
Given an array nums and an integer target.
Return the maximum number of non-empty non-overlapping subarrays such that the sum of values in each subarray is equal to target.

Example 1:
Input: nums = [1,1,1,1,1], target = 2
Output: 2
Explanation: There are 2 non-overlapping subarrays [1,1,1,1,1] with sum equals to target(2).

Example 2:
Input: nums = [-1,3,5,1,4,2,-9], target = 6
Output: 2
Explanation: There are 3 subarrays with sum equal to 6.
([5,1], [4,2], [3,5,1,4,2,-9]) but only the first 2 are non-overlapping.
Example 3:
Input: nums = [-2,6,6,3,5,4,1,2,8], target = 10
Output: 3

Example 4:
Input: nums = [0,0,0], target = 0
Output: 3

Constraints:

1 <= nums.length <= 10^5
-10^4 <= nums[i] <= 10^4
0 <= target <= 10^6
-/

def max_non_overlapping (nums: List Int) (target: Int) : Nat :=
  sorry

def abs (n: Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_list (l: List Nat) : Nat :=
  sorry

theorem max_non_overlapping_non_negative (nums: List Int) (target: Int) :
  max_non_overlapping nums target ≥ 0 :=
sorry

theorem max_non_overlapping_bounded_by_length (nums: List Int) (target: Int) :
  max_non_overlapping nums target ≤ nums.length :=
sorry

theorem max_non_overlapping_empty_list (target: Int) :
  max_non_overlapping [] target = 0 :=
sorry

theorem max_non_overlapping_all_zeros (n: Nat) :
  max_non_overlapping (List.replicate n 0) 0 = n :=
sorry

theorem max_non_overlapping_self_consistent (nums: List Int) (target: Int) :
  max_non_overlapping nums target = max_non_overlapping nums target :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_non_overlapping [1, 1, 1, 1, 1] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_non_overlapping [-1, 3, 5, 1, 4, 2, -9] 6

/-
info: 3
-/
-- #guard_msgs in
-- #eval max_non_overlapping [0, 0, 0] 0

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible