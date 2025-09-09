-- <vc-helpers>
-- </vc-helpers>

def calculate_maintenance_due (n : Nat) (payments : List String) : Nat :=
  sorry

theorem empty_payments (n : Nat) :
  calculate_maintenance_due n [] = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_maintenance_due 2 ["1", "1"]

/-
info: 2200
-/
-- #guard_msgs in
-- #eval calculate_maintenance_due 2 ["0", "0"]

/-
info: 2300
-/
-- #guard_msgs in
-- #eval calculate_maintenance_due 3 ["0", "1", "0"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible