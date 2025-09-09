-- <vc-helpers>
-- </vc-helpers>

def is_prime (n : Nat) : Bool := sorry

def sqrt (n : Nat) : Nat := sorry

theorem non_positive_numbers_not_prime {n : Nat} (h : n ≤ 1) : 
  is_prime n = false := sorry

theorem prime_divisibility_true {n : Nat} (h1 : n ≥ 2) (h2 : is_prime n = true) :
  ∀ i, 2 ≤ i → i ≤ sqrt n → n % i ≠ 0 := sorry

theorem prime_divisibility_false {n : Nat} (h1 : n ≥ 2) (h2 : is_prime n = false) :
  ∃ i, 2 ≤ i ∧ i ≤ sqrt n ∧ n % i = 0 := sorry

theorem even_numbers_not_prime {n : Nat} (h1 : n > 2) (h2 : n % 2 = 0) :
  is_prime n = false := sorry

theorem perfect_squares_not_prime {n : Nat} (h1 : n > 4) 
  (h2 : ∃ k, n = k * k) : is_prime n = false := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime 0

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime 1

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime 2

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime 11

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime 61

/-
info: True
-/
-- #guard_msgs in
-- #eval is_prime 571

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime 12

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime 573

/-
info: False
-/
-- #guard_msgs in
-- #eval is_prime 25

-- Apps difficulty: introductory
-- Assurance level: unguarded