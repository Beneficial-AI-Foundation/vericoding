-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_nth_sequence_element (n : Nat) : Nat := sorry

/- Theorems -/
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible