/-
Given an array of integers nums, find the maximum length of a subarray where the product of all its elements is positive.
A subarray of an array is a consecutive sequence of zero or more values taken out of that array.
Return the maximum length of a subarray with positive product.

Example 1:
Input: nums = [1,-2,-3,4]
Output: 4
Explanation: The array nums already has a positive product of 24.

Example 2:
Input: nums = [0,1,-2,-3,-4]
Output: 3
Explanation: The longest subarray with positive product is [1,-2,-3] which has a product of 6.
Notice that we cannot include 0 in the subarray since that'll make the product 0 which is not positive.
Example 3:
Input: nums = [-1,-2,-3,0,1]
Output: 2
Explanation: The longest subarray with positive product is [-1,-2] or [-2,-3].

Example 4:
Input: nums = [-1,2]
Output: 1

Example 5:
Input: nums = [1,2,3,5,-6,4,0,10]
Output: 4

Constraints:

1 <= nums.length <= 10^5
-10^9 <= nums[i] <= 10^9
-/

-- <vc-helpers>
-- </vc-helpers>

def getMaxLen (nums : List Int) : Nat :=
  sorry

theorem getMaxLen_nonnegative (nums : List Int) : 
  getMaxLen nums ≥ 0 := sorry

theorem getMaxLen_upper_bound (nums : List Int) :
  getMaxLen nums ≤ nums.length := sorry

theorem getMaxLen_all_zeros {nums : List Int} (h : ∀ x ∈ nums, x = 0) : 
  getMaxLen nums = 0 := sorry

theorem getMaxLen_zeros_only (n : Nat) : 
  getMaxLen (List.replicate n 0) = 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval getMaxLen [1, -2, -3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval getMaxLen [0, 1, -2, -3, -4]

/-
info: 2
-/
-- #guard_msgs in
-- #eval getMaxLen [-1, -2, -3, 0, 1]

-- Apps difficulty: interview
-- Assurance level: unguarded