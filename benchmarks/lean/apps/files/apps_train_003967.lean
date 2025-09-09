def is_prime : Nat → Bool := sorry

def factorial (n : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def factors_up_to (n : Nat) (k : Nat) : Bool := sorry

theorem not_prime_if_less_than_2 (n : Nat) (h : n ≤ 1) : ¬(is_prime n = true) := sorry

theorem prime_iff_no_factors (n : Nat) (h : n ≥ 2) :
  is_prime n = true ↔ ¬(factors_up_to n (n/2) = true) := sorry

theorem wilson_prime_property (n : Nat) (h1 : n ≥ 2) (h2 : n ≤ 20) :
  is_prime n = true → (factorial (n-1) + 1) % n = 0 := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime 2

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime 29

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime 143

-- Apps difficulty: introductory
-- Assurance level: unguarded