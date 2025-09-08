/-
For "x", determine how many positive integers less than or equal to "x" are odd but not prime. Assume "x" is an integer between 1 and 10000.

Example: 5 has three odd numbers (1,3,5) and only the number 1 is not prime, so the answer is 1

Example: 10 has five odd numbers (1,3,5,7,9) and only 1 and 9 are not prime, so the answer is 2
-/

-- <vc-helpers>
-- </vc-helpers>

def odd_not_prime (n : Nat) : Nat := sorry
def not_prime (n : Nat) : Bool := sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible