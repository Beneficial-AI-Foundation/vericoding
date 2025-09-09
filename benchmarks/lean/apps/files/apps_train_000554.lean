-- <vc-helpers>
-- </vc-helpers>

def find_nth_sequence_element (n : Nat) : Nat := sorry

/- Theorems -/

theorem output_less_than_input {n : Nat} (h : n > 0) : 
  find_nth_sequence_element n < n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_nth_sequence_element 8

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_nth_sequence_element 9

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_nth_sequence_element 20

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible