-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_minimum_donation (x : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_geq_input (x : Nat) (h : x > 0) :
  find_minimum_donation x ≥ x :=
sorry

theorem result_is_power_of_2 (x : Nat) (h : x > 0) :
  (find_minimum_donation x &&& (find_minimum_donation x - 1)) = 0 :=
sorry

theorem result_is_minimal (x : Nat) (h : x > 0) :
  find_minimum_donation x / 2 < x ∨ find_minimum_donation x = x :=
sorry

theorem power_2_input_unchanged (x : Nat) (h : x > 0) (h2 : (x &&& (x - 1)) = 0) :
  find_minimum_donation x = x :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_minimum_donation 3

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_minimum_donation 7

/-
info: 16
-/
-- #guard_msgs in
-- #eval find_minimum_donation 15
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible