-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_latest_step (arr : List Nat) (target : Nat) : Int := sorry 

theorem find_latest_step_basic_cases_1 :
  find_latest_step [3,5,1,2,4] 1 = 4 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_latest_step_basic_cases_2 :
  find_latest_step [3,1,5,4,2] 2 = -1 := 
sorry

theorem find_latest_step_basic_cases_3 :
  find_latest_step [1] 1 = 1 :=
sorry

theorem find_latest_step_basic_cases_4 :
  find_latest_step [2,1] 2 = 2 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_latest_step [3, 5, 1, 2, 4] 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_latest_step [3, 1, 5, 4, 2] 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_latest_step [1] 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible