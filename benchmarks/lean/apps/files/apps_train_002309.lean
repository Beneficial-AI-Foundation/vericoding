/-
Given an array of size n, find the majority element. The majority element is the element that appears more than ⌊ n/2 ⌋ times.

You may assume that the array is non-empty and the majority element always exist in the array.

Example 1:

Input: [3,2,3]
Output: 3

Example 2:

Input: [2,2,1,1,1,2,2]
Output: 2
-/

-- <vc-helpers>
-- </vc-helpers>

def majorityElement (xs : List Int) : Int :=
  sorry

theorem single_element_majority {x : Int} :
  majorityElement [x] = x :=
  sorry

theorem repeated_element_majority (lst : List Int) (x : Int) :
  majorityElement (List.replicate (lst.length + 1) x) = x :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval majority_element [3, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval majority_element [2, 2, 1, 1, 1, 2, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval majority_element [1]

-- Apps difficulty: introductory
-- Assurance level: unguarded