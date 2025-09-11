-- <vc-preamble>
def sqrt (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_of_open_lockers (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_open_lockers_is_floor_sqrt (n : Nat) :
  num_of_open_lockers n = sqrt n :=
sorry

theorem num_open_lockers_nonnegative (n : Nat) :
  num_of_open_lockers n ≥ 0 :=
sorry

theorem num_open_lockers_squared_bound (n : Nat) :
  (num_of_open_lockers n) * (num_of_open_lockers n) ≤ n :=
sorry

theorem num_open_lockers_next_squared_bound (n : Nat) :
  (num_of_open_lockers n + 1) * (num_of_open_lockers n + 1) > n :=
sorry

theorem num_open_lockers_zero :
  num_of_open_lockers 0 = 0 :=
sorry

theorem num_open_lockers_one : 
  num_of_open_lockers 1 = 1 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval num_of_open_lockers 0

/-
info: 2
-/
-- #guard_msgs in
-- #eval num_of_open_lockers 4

/-
info: 22
-/
-- #guard_msgs in
-- #eval num_of_open_lockers 500
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded