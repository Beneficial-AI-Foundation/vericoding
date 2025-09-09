-- <vc-helpers>
-- </vc-helpers>

def faulty_odometer (n : Nat) : Nat :=
  sorry

theorem odometer_never_negative (n : Nat) : 
  faulty_odometer n ≥ 0 :=
sorry

theorem odometer_always_smaller (n : Nat) :
  faulty_odometer n ≤ n :=
sorry

theorem odometer_consistent (n : Nat) :
  faulty_odometer n = faulty_odometer n :=
sorry

theorem odometer_zero :
  faulty_odometer 0 = 0 :=
sorry

/-
info: 12
-/
-- #guard_msgs in
-- #eval faulty_odometer 13

/-
info: 13
-/
-- #guard_msgs in
-- #eval faulty_odometer 15

/-
info: 1462
-/
-- #guard_msgs in
-- #eval faulty_odometer 2005

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible