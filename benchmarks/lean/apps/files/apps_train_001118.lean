-- <vc-preamble>
def solve_helper_thanks (n : Int) : String := sorry

theorem solve_helper_thanks_result_valid (n : Int) :
  (solve_helper_thanks n = "-1") ∨ 
  (solve_helper_thanks n = "Thanks for helping Chef!") := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_multiple_cases (nums : List Int) : List String := sorry 

theorem solve_multiple_cases_length (nums : List Int) :
  (solve_multiple_cases nums).length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_helper_thanks_condition (n : Int) :
  (n < 10) = (solve_helper_thanks n = "Thanks for helping Chef!") := sorry

theorem solve_multiple_cases_valid_results (nums : List Int) :
  ∀ x ∈ solve_multiple_cases nums, 
    (x = "-1") ∨ (x = "Thanks for helping Chef!") := sorry

theorem solve_multiple_cases_condition (nums : List Int) :
  ∀ (i : Nat), i < nums.length →
    ((nums[i]! < 10) = 
     ((solve_multiple_cases nums)[i]! = "Thanks for helping Chef!")) := sorry

/-
info: test1_expected
-/
-- #guard_msgs in
-- #eval solve_multiple_cases [1, 12, -5]

/-
info: test2_expected
-/
-- #guard_msgs in
-- #eval solve_multiple_cases [-20, 0, 20]

/-
info: test3_expected
-/
-- #guard_msgs in
-- #eval solve_multiple_cases [9, 10]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded