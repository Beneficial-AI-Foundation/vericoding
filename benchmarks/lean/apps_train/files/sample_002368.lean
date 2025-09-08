/-
Given an array of integers arr, write a function that returns true if and only if the number of occurrences of each value in the array is unique.

Example 1:
Input: arr = [1,2,2,1,1,3]
Output: true
Explanation: The value 1 has 3 occurrences, 2 has 2 and 3 has 1. No two values have the same number of occurrences.
Example 2:
Input: arr = [1,2]
Output: false

Example 3:
Input: arr = [-3,0,1,-3,1,1,1,-3,10,0]
Output: true

Constraints:

1 <= arr.length <= 1000
-1000 <= arr[i] <= 1000
-/

-- <vc-helpers>
-- </vc-helpers>

def uniqueOccurrences (arr : List Int) : Bool :=
  sorry

theorem uniqueOccurrences_returns_bool (arr : List Int) :
  uniqueOccurrences arr = true ∨ uniqueOccurrences arr = false := by
  sorry

theorem uniqueOccurrences_empty_array :
  uniqueOccurrences [] = true := by
  sorry

theorem uniqueOccurrences_single_element (x : Int) :
  uniqueOccurrences [x] = true := by
  sorry

theorem uniqueOccurrences_reverse (arr : List Int) :
  uniqueOccurrences arr = uniqueOccurrences arr.reverse := by
  sorry

theorem uniqueOccurrences_double (arr : List Int) :
  uniqueOccurrences arr = uniqueOccurrences (arr ++ arr) := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval unique_occurrences [1, 2, 2, 1, 1, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval unique_occurrences [1, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval unique_occurrences [-3, 0, 1, -3, 1, 1, 1, -3, 10, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded