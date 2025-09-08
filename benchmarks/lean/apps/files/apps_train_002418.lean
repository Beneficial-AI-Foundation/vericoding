/-
Given an array of integers arr, a lucky integer is an integer which has a frequency in the array equal to its value.
Return a lucky integer in the array. If there are multiple lucky integers return the largest of them. If there is no lucky integer return -1.

Example 1:
Input: arr = [2,2,3,4]
Output: 2
Explanation: The only lucky number in the array is 2 because frequency[2] == 2.

Example 2:
Input: arr = [1,2,2,3,3,3]
Output: 3
Explanation: 1, 2 and 3 are all lucky numbers, return the largest of them.

Example 3:
Input: arr = [2,2,2,3,3]
Output: -1
Explanation: There are no lucky numbers in the array.

Example 4:
Input: arr = [5]
Output: -1

Example 5:
Input: arr = [7,7,7,7,7,7,7]
Output: 7

Constraints:

1 <= arr.length <= 500
1 <= arr[i] <= 500
-/

-- <vc-helpers>
-- </vc-helpers>

def find_lucky (arr : List Nat) : Int := sorry

theorem find_lucky_lower_bound (arr : List Nat) : 
  find_lucky arr ≥ -1 := sorry

theorem find_lucky_freq_match (arr : List Nat) :
  find_lucky arr ≠ -1 → 
  (arr.countP (· = (find_lucky arr).toNat)) = (find_lucky arr).toNat := sorry 

theorem find_lucky_is_max (arr : List Nat) (n : Nat) :
  n ∈ arr → 
  (arr.countP (· = n)) = n →
  n ≤ (find_lucky arr).toNat := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_lucky [2, 2, 3, 4]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_lucky [1, 2, 2, 3, 3, 3]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_lucky [2, 2, 2, 3, 3]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible