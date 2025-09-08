/-
Given an unsorted array of integers, find the length of the longest consecutive elements sequence.

Your algorithm should run in O(n) complexity.

Example:

Input: [100, 4, 200, 1, 3, 2]
Output: 4
Explanation: The longest consecutive elements sequence is [1, 2, 3, 4]. Therefore its length is 4.
-/

def longest_consecutive (nums : List Int) : Nat := sorry

theorem output_nonnegative (nums : List Int) : 
  longest_consecutive nums ≥ 0 := sorry

def removeDuplicates (nums : List Int) : List Int := sorry

theorem same_as_deduplicated (nums : List Int) :
  longest_consecutive nums = longest_consecutive (removeDuplicates nums) := sorry

-- <vc-helpers>
-- </vc-helpers>

def sortList (nums : List Int) : List Int := sorry 

theorem sorted_same_as_unsorted (nums : List Int) :
  nums ≠ [] → longest_consecutive nums = longest_consecutive (sortList nums) := sorry

theorem output_leq_input_len (nums : List Int) :
  longest_consecutive nums ≤ nums.length := sorry

theorem empty_list_zero (nums : List Int) :
  nums = [] → longest_consecutive nums = 0 := sorry

theorem single_element_one (nums : List Int) (x : Int) :
  nums = [x] → longest_consecutive nums = 1 := sorry

theorem reversed_same (nums : List Int) :
  nums ≠ [] → longest_consecutive nums = longest_consecutive nums.reverse := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval longest_consecutive [100, 4, 200, 1, 3, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_consecutive [1, 2, 0, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval longest_consecutive []

-- Apps difficulty: interview
-- Assurance level: unguarded