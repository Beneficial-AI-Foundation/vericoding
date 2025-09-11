-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_kth_number (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_kth_number_fixed_cases :
  find_kth_number 13 2 = 10 ∧ 
  find_kth_number 10 3 = 2 ∧
  find_kth_number 100 10 = 17 ∧
  find_kth_number 20 1 = 1 ∧
  find_kth_number 50 5 = 13 := by
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval find_kth_number 13 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_kth_number 10 3

/-
info: 17
-/
-- #guard_msgs in
-- #eval find_kth_number 100 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded