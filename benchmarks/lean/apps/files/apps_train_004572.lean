def is_prime : Nat → Bool := sorry

def reverse : Nat → Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def backwards_prime : Nat → Nat → List Nat := sorry

theorem backwards_prime_empty_range : 
  backwards_prime 1 0 = [] ∧ 
  backwards_prime 0 1 = [] := sorry

/-
info: [13, 17, 31, 37, 71, 73, 79, 97]
-/
-- #guard_msgs in
-- #eval backwards_prime 2 100

/-
info: [9923, 9931, 9941, 9967]
-/
-- #guard_msgs in
-- #eval backwards_prime 9900 10000

/-
info: []
-/
-- #guard_msgs in
-- #eval backwards_prime 501 599

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible