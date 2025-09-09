def maxLen : Nat :=
sorry

def sum_squares (n : Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def square_pi (n : Nat) : Nat :=
sorry

theorem square_pi_monotone {n₁ n₂ : Nat} (h : n₁ ≤ n₂) (h2 : n₂ ≤ maxLen) :
  square_pi n₁ ≤ square_pi n₂ :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval square_pi 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval square_pi 3

/-
info: 8
-/
-- #guard_msgs in
-- #eval square_pi 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible