-- <vc-helpers>
-- </vc-helpers>

def is_prime_happy : Int → Bool := sorry

theorem is_prime_happy_returns_bool (n : Int) :
  is_prime_happy n = true ∨ is_prime_happy n = false := sorry

theorem known_true_values (n : Int) (h : n > 0) :
  n = 5 ∨ n = 25 ∨ n = 32 ∨ n = 71 ∨ n = 2745 ∨ n = 10623 ∨ n = 63201 ∨ n = 85868 →
  is_prime_happy n = true := sorry

theorem output_is_deterministic (n : Int) :
  is_prime_happy n = is_prime_happy n := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime_happy 5

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime_happy 8

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime_happy 25

-- Apps difficulty: introductory
-- Assurance level: unguarded