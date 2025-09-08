/-
Given an integer array nums and an integer k, return the maximum sum of a non-empty subsequence of that array such that for every two consecutive integers in the subsequence, nums[i] and nums[j], where i < j, the condition j - i <= k is satisfied.
A subsequence of an array is obtained by deleting some number of elements (can be zero) from the array, leaving the remaining elements in their original order.

Example 1:
Input: nums = [10,2,-10,5,20], k = 2
Output: 37
Explanation: The subsequence is [10, 2, 5, 20].

Example 2:
Input: nums = [-1,-2,-3], k = 1
Output: -1
Explanation: The subsequence must be non-empty, so we choose the largest number.

Example 3:
Input: nums = [10,-2,-10,-5,20], k = 2
Output: 23
Explanation: The subsequence is [10, -2, -5, 20].

Constraints:

1 <= k <= nums.length <= 10^5
-10^4 <= nums[i] <= 10^4
-/

-- <vc-helpers>
-- </vc-helpers>

def constrained_max_subset_sum (nums : List Int) (k : Nat) : Int := sorry

theorem constrained_max_subset_sum_ge_max_single (nums : List Int) (k : Nat) 
    (h : nums ≠ []) (hk : k > 0) :
    ∀ x ∈ nums, constrained_max_subset_sum nums k ≥ x := sorry

theorem constrained_max_subset_sum_all_negative (nums : List Int) (k : Nat)
    (h : nums ≠ []) (hk : k > 0) (h_neg : ∀ x ∈ nums, x < 0) :
    ∃ x ∈ nums, constrained_max_subset_sum nums k = x := sorry

theorem constrained_max_subset_sum_independence (nums : List Int) (k : Nat)
    (h : nums.length > k + 1) (hk : k > 0) :
    let nums_modified := (nums.take (k+1)).append (List.replicate (nums.length - k - 1) (-1000))
    constrained_max_subset_sum (nums.take (k+1)) k = constrained_max_subset_sum nums_modified k := sorry

/-
info: 37
-/
-- #guard_msgs in
-- #eval constrained_max_subset_sum [10, 2, -10, 5, 20] 2

/-
info: -1
-/
-- #guard_msgs in
-- #eval constrained_max_subset_sum [-1, -2, -3] 1

/-
info: 23
-/
-- #guard_msgs in
-- #eval constrained_max_subset_sum [10, -2, -10, -5, 20] 2

-- Apps difficulty: interview
-- Assurance level: unguarded