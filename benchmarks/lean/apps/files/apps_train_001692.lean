-- <vc-helpers>
-- </vc-helpers>

def find_sequence_value (n : Nat) : Nat := sorry

theorem sequence_bounded (n : Nat) :
  let result := find_sequence_value n
  0 ≤ result ∧ result ≤ n := sorry

theorem base_cases :
  find_sequence_value 0 = 0 ∧
  find_sequence_value 1 = 1 ∧
  find_sequence_value 2 = 2 ∧ 
  find_sequence_value 3 = 2 := sorry

theorem sequence_monotonic (n : Nat) :
  n ≥ 4 →
  find_sequence_value n ≥ find_sequence_value (n-1) := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_sequence_value 0

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_sequence_value 3

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_sequence_value 10

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible