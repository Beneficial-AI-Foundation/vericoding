-- <vc-helpers>
-- </vc-helpers>

def numOfMinutes (n : Nat) (headID : Nat) (manager : List Int) (informTime : List Nat) : Nat :=
  sorry

theorem single_employee_zero_time {n : Nat} (h : n = 1) :
  numOfMinutes 1 0 [-1] [0] = 0 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval numOfMinutes 1 0 [-1] [0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval numOfMinutes 6 2 [2, 2, -1, 2, 2, 2] [0, 0, 1, 0, 0, 0]

/-
info: 21
-/
-- #guard_msgs in
-- #eval numOfMinutes 7 6 [1, 2, 3, 4, 5, 6, -1] [0, 6, 5, 4, 3, 2, 1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible