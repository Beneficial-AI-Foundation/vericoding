def get_number_of_squares (n : Int) : Nat :=
  sorry

def sum_squares (n : Nat) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def next_square (n : Nat) : Int :=
  sorry

theorem known_sequence_values :
  (get_number_of_squares 1 = 0) ∧
  (get_number_of_squares 2 = 1) ∧ 
  (get_number_of_squares 6 = 2) ∧
  (get_number_of_squares 15 = 3) :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_number_of_squares 6

/-
info: 3
-/
-- #guard_msgs in
-- #eval get_number_of_squares 15

/-
info: 6
-/
-- #guard_msgs in
-- #eval get_number_of_squares 100

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible