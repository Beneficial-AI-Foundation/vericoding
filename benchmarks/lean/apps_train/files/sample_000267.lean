/-
Given an array of integers nums and an integer limit, return the size of the longest non-empty subarray such that the absolute difference between any two elements of this subarray is less than or equal to limit.

Example 1:
Input: nums = [8,2,4,7], limit = 4
Output: 2 
Explanation: All subarrays are: 
[8] with maximum absolute diff |8-8| = 0 <= 4.
[8,2] with maximum absolute diff |8-2| = 6 > 4. 
[8,2,4] with maximum absolute diff |8-2| = 6 > 4.
[8,2,4,7] with maximum absolute diff |8-2| = 6 > 4.
[2] with maximum absolute diff |2-2| = 0 <= 4.
[2,4] with maximum absolute diff |2-4| = 2 <= 4.
[2,4,7] with maximum absolute diff |2-7| = 5 > 4.
[4] with maximum absolute diff |4-4| = 0 <= 4.
[4,7] with maximum absolute diff |4-7| = 3 <= 4.
[7] with maximum absolute diff |7-7| = 0 <= 4. 
Therefore, the size of the longest subarray is 2.

Example 2:
Input: nums = [10,1,2,4,7,2], limit = 5
Output: 4 
Explanation: The subarray [2,4,7,2] is the longest since the maximum absolute diff is |2-7| = 5 <= 5.

Example 3:
Input: nums = [4,2,2,2,4,4,2,2], limit = 0
Output: 3

Constraints:

1 <= nums.length <= 10^5
1 <= nums[i] <= 10^9
0 <= limit <= 10^9
-/

def maxEqualSeq : List Int → Nat 
  | [] => 1
  | [x] => 1 
  | x::y::xs => if x = y 
                then 1 + maxEqualSeq (y::xs)
                else max 1 (maxEqualSeq (y::xs))

-- <vc-helpers>
-- </vc-helpers>

def longestSubarray (nums : List Int) (limit : Nat) : Nat := sorry

theorem longestSubarray_result_bounds 
  {nums : List Int} {limit : Nat} (h : nums ≠ []) : 
  1 ≤ (longestSubarray nums limit) ∧ (longestSubarray nums limit) ≤ nums.length := sorry

/- There exists a valid subarray of length equal to the result -/

theorem longestSubarray_exists_valid_window
  {nums : List Int} {limit : Nat} (h : nums ≠ []) :
  ∃ i, i + (longestSubarray nums limit) ≤ nums.length ∧ 
    let window := nums.take (i + (longestSubarray nums limit)) |>.drop i
    (window.maximum? |>.getD 0) - (window.minimum? |>.getD 0) ≤ limit := sorry

/- No larger valid window exists -/

theorem longestSubarray_optimal
  {nums : List Int} {limit : Nat} (h : nums ≠ []) :
  ∀ i len, i + len ≤ nums.length → len > (longestSubarray nums limit) →
    let window := nums.take (i + len) |>.drop i
    (window.maximum? |>.getD 0) - (window.minimum? |>.getD 0) > limit := sorry

/- For zero limit, result equals longest sequence of equal numbers -/

theorem longestSubarray_zero_limit
  {nums : List Int} (h : nums ≠ []) :
  longestSubarray nums 0 = maxEqualSeq nums := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval longestSubarray [8, 2, 4, 7] 4

/-
info: 4
-/
-- #guard_msgs in
-- #eval longestSubarray [10, 1, 2, 4, 7, 2] 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval longestSubarray [4, 2, 2, 2, 4, 4, 2, 2] 0

-- Apps difficulty: interview
-- Assurance level: unguarded