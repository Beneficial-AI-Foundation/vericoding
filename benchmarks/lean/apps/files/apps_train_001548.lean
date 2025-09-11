-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_most_common_divisor (l r : Nat) : Nat := sorry

theorem single_number_returns_itself (x : Nat)
  (h : x > 0) : find_most_common_divisor x x = x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem range_output_is_positive (l r : Nat)
  (h₁ : l > 0) (h₂ : r > 0) : find_most_common_divisor l r > 0 := sorry

theorem range_output_less_than_max_input (l r : Nat)  
  (h₁ : l > 0) (h₂ : r > 0) : find_most_common_divisor l r ≤ max l r := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_most_common_divisor 19 29

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_most_common_divisor 3 6

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_most_common_divisor 5 5
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible