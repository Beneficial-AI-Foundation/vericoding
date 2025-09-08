/-
Given an array of integers arr and two integers k and threshold.
Return the number of sub-arrays of size k and average greater than or equal to threshold.

Example 1:
Input: arr = [2,2,2,2,5,5,5,8], k = 3, threshold = 4
Output: 3
Explanation: Sub-arrays [2,5,5],[5,5,5] and [5,5,8] have averages 4, 5 and 6 respectively. All other sub-arrays of size 3 have averages less than 4 (the threshold).

Example 2:
Input: arr = [1,1,1,1,1], k = 1, threshold = 0
Output: 5

Example 3:
Input: arr = [11,13,17,23,29,31,7,5,2,3], k = 3, threshold = 5
Output: 6
Explanation: The first 6 sub-arrays of size 3 have averages greater than 5. Note that averages are not integers.

Example 4:
Input: arr = [7,7,7,7,7,7,7], k = 7, threshold = 7
Output: 1

Example 5:
Input: arr = [4,4,4,4], k = 4, threshold = 1
Output: 1

Constraints:

1 <= arr.length <= 10^5
1 <= arr[i] <= 10^4
1 <= k <= arr.length
0 <= threshold <= 10^4
-/

-- <vc-helpers>
-- </vc-helpers>

def num_of_subarrays (arr : List Int) (k : Nat) (threshold : Int) : Nat :=
sorry

theorem non_negative_result (arr : List Int) (k : Nat) (threshold : Int) :
  num_of_subarrays arr k threshold ≥ 0 :=
sorry

theorem empty_result_if_smaller (arr : List Int) (k : Nat) (threshold : Int) :
  arr.length < k → num_of_subarrays arr k threshold = 0 :=
sorry

theorem result_bounded_by_possible_subarrays (arr : List Int) (k : Nat) (threshold : Int) :
  arr.length ≥ k → num_of_subarrays arr k threshold ≤ arr.length - k + 1 :=
sorry

theorem k_equals_one_case (arr : List Int) (threshold : Int) :
  num_of_subarrays arr 1 threshold = (arr.filter (fun x => x ≥ threshold)).length :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval num_of_subarrays [2, 2, 2, 2, 5, 5, 5, 8] 3 4

/-
info: 5
-/
-- #guard_msgs in
-- #eval num_of_subarrays [1, 1, 1, 1, 1] 1 0

/-
info: 6
-/
-- #guard_msgs in
-- #eval num_of_subarrays [11, 13, 17, 23, 29, 31, 7, 5, 2, 3] 3 5

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible