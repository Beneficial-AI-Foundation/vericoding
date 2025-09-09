-- <vc-helpers>
-- </vc-helpers>

def isPrime (n : Nat) : Bool := sorry
def last_digit_prime_sum (n : Nat) : Nat := sorry

-- Results are natural numbers between 0 and 9 inclusive

theorem last_digit_bounds (n : Nat) (h : n ≥ 2) : 
  0 ≤ last_digit_prime_sum n ∧ last_digit_prime_sum n ≤ 9 := sorry

-- Known value cases

theorem small_primes_cases : 
  last_digit_prime_sum 2 = 2 ∧ 
  last_digit_prime_sum 3 = 5 ∧
  last_digit_prime_sum 4 = 5 ∧
  last_digit_prime_sum 5 = 0 := sorry

-- Result is equal to its modulo 10

theorem modulo_property (n : Nat) (h : n ≥ 2) :
  last_digit_prime_sum n = last_digit_prime_sum n % 10 := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval last_digit_prime_sum 10

/-
info: 0
-/
-- #guard_msgs in
-- #eval last_digit_prime_sum 5

/-
info: 0
-/
-- #guard_msgs in
-- #eval last_digit_prime_sum 100

-- Apps difficulty: interview
-- Assurance level: guarded