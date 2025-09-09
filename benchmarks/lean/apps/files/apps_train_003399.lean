-- <vc-helpers>
-- </vc-helpers>

def binary_array_to_number (arr : List Nat) : Nat :=
  sorry

theorem binary_array_to_number_zero :
  binary_array_to_number [0] = 0 :=
sorry

theorem binary_array_to_number_one :
  binary_array_to_number [1] = 1 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval binary_array_to_number [0, 0, 0, 1]

/-
info: 6
-/
-- #guard_msgs in
-- #eval binary_array_to_number [0, 1, 1, 0]

/-
info: 15
-/
-- #guard_msgs in
-- #eval binary_array_to_number [1, 1, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible