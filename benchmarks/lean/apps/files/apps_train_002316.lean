-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_single_number (nums: List Int) : Int := sorry

theorem find_single_number_pairs_plus_single (single: Int) (pairs: List Int) :
  find_single_number (pairs ++ pairs ++ [single]) = single := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded