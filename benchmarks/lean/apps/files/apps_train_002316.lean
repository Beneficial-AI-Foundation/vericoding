/-
Given a non-empty array of integers, every element appears twice except for one. Find that single one.

Note:

Your algorithm should have a linear runtime complexity. Could you implement it without using extra memory?

Example 1:

Input: [2,2,1]
Output: 1

Example 2:

Input: [4,1,2,1,2]
Output: 4
-/

-- <vc-helpers>
-- </vc-helpers>

def find_single_number (nums: List Int) : Int := sorry

theorem find_single_number_pairs_plus_single (single: Int) (pairs: List Int) :
  find_single_number (pairs ++ pairs ++ [single]) = single := sorry

theorem find_single_number_single_element (x: Int) :
  find_single_number [x] = x := sorry

theorem find_single_number_input_parity (nums: List Int) (h: nums ≠ []) :
  let nums_with_pairs := nums ++ (List.take (nums.length - 1) nums)
  List.length nums_with_pairs % 2 = 1 ∧ 
  find_single_number nums_with_pairs = List.get! nums (nums.length - 1) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_single_number [2, 2, 1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_single_number [4, 1, 2, 1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_single_number [1]

-- Apps difficulty: introductory
-- Assurance level: guarded