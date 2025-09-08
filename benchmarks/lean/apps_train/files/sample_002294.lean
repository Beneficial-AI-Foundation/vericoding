/-
Let's call an array arr a mountain if the following properties hold:

arr.length >= 3
There exists some i with 0 < i < arr.length - 1 such that:

arr[0] < arr[1] < ... arr[i-1] < arr[i] 
arr[i] > arr[i+1] > ... > arr[arr.length - 1]

Given an integer array arr that is guaranteed to be a mountain, return any i such that arr[0] < arr[1] < ... arr[i - 1] < arr[i] > arr[i + 1] > ... > arr[arr.length - 1].

Example 1:
Input: arr = [0,1,0]
Output: 1
Example 2:
Input: arr = [0,2,1,0]
Output: 1
Example 3:
Input: arr = [0,10,5,2]
Output: 1
Example 4:
Input: arr = [3,4,5,1]
Output: 2
Example 5:
Input: arr = [24,69,100,99,79,78,67,36,26,19]
Output: 2

Constraints:

3 <= arr.length <= 104
0 <= arr[i] <= 106
arr is guaranteed to be a mountain array.
-/

-- <vc-helpers>
-- </vc-helpers>

def peak_index_in_mountain_array (arr : List Int) : Nat :=
sorry

theorem peak_index_not_at_edges {arr : List Int} (h: arr.length ≥ 3)
  (hm: ∃ i, 0 < i ∧ i < arr.length - 1 ∧ 
    (∀ j < i, arr[j]! < arr[j+1]!) ∧ 
    (∀ j, i ≤ j ∧ j < arr.length - 1 → arr[j]! > arr[j+1]!)) :
  let peak := peak_index_in_mountain_array arr
  0 < peak ∧ peak < arr.length - 1 :=
sorry

theorem peak_greater_than_left {arr : List Int} (h: arr.length ≥ 3)
  (hm: ∃ i, 0 < i ∧ i < arr.length - 1 ∧ 
    (∀ j < i, arr[j]! < arr[j+1]!) ∧ 
    (∀ j, i ≤ j ∧ j < arr.length - 1 → arr[j]! > arr[j+1]!)) :
  let peak := peak_index_in_mountain_array arr
  arr[peak]! > arr[peak-1]! :=
sorry

theorem peak_greater_than_right {arr : List Int} (h: arr.length ≥ 3) 
  (hm: ∃ i, 0 < i ∧ i < arr.length - 1 ∧ 
    (∀ j < i, arr[j]! < arr[j+1]!) ∧ 
    (∀ j, i ≤ j ∧ j < arr.length - 1 → arr[j]! > arr[j+1]!)) :
  let peak := peak_index_in_mountain_array arr
  arr[peak]! > arr[peak+1]! :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval peak_index_in_mountain_array [0, 1, 0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval peak_index_in_mountain_array [0, 2, 1, 0]

/-
info: 2
-/
-- #guard_msgs in
-- #eval peak_index_in_mountain_array [24, 69, 100, 99, 79, 78, 67, 36, 26, 19]

-- Apps difficulty: introductory
-- Assurance level: unguarded