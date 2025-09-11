-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_of_squares (l w : Nat) : Nat := sorry

theorem square_input (n : Nat) (h : n > 0) :
  number_of_squares n n = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem commutative (l w : Nat) (h₁ : l > 0) (h₂ : w > 0) :
  number_of_squares l w = number_of_squares w l := sorry

theorem output_bounds (l w : Nat) (h₁ : l > 0) (h₂ : w > 0) :
  1 ≤ number_of_squares l w ∧ number_of_squares l w ≤ l * w := sorry

theorem scaling (l factor : Nat) (h₁ : l > 0) (h₂ : factor > 0) :
  number_of_squares (l * factor) (l * factor) = number_of_squares l l := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval number_of_squares 2 2

/-
info: 6
-/
-- #guard_msgs in
-- #eval number_of_squares 6 9

/-
info: 6
-/
-- #guard_msgs in
-- #eval number_of_squares 4 6
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible