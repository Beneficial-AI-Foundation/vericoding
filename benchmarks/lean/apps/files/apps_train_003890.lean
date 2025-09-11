-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_not_prime (n : Nat) : Nat := sorry
def not_prime (n : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_not_prime_increasing (n : Nat) (h : n > 0) :
  odd_not_prime n ≥ odd_not_prime (n-1) := sorry

theorem odd_not_prime_bounds (n : Nat) (h : n > 0) :
  odd_not_prime n ≥ 0 ∧ odd_not_prime n ≤ (n+1)/2 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval odd_not_prime 5

/-
info: 2
-/
-- #guard_msgs in
-- #eval odd_not_prime 10

/-
info: 26
-/
-- #guard_msgs in
-- #eval odd_not_prime 99
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible