-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Nat := sorry

def check_sum_of_primes (n k : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_prime_properties (n : Nat) (h : n ≤ 1000) :
  (is_prime n = 0 ∨ is_prime n = 1) ∧
  (n ≤ 1 → is_prime n = 0) ∧ 
  (n = 2 → is_prime n = 1) ∧
  (n > 2 ∧ n % 2 = 0 → is_prime n = 0) := sorry

theorem check_sum_of_primes_properties (n k : Nat) 
  (hn : n ≤ 1000) (hk : k ≤ 10) :
  (check_sum_of_primes n k = 0 ∨ check_sum_of_primes n k = 1) ∧
  (n < 2 * k → check_sum_of_primes n k = 0) ∧
  (k = 1 → check_sum_of_primes n k = is_prime n) ∧
  (k = 2 ∧ n % 2 = 0 → check_sum_of_primes n k = 1) := sorry

theorem check_sum_of_primes_k1 (n : Nat) 
  (h1 : n ≥ 3) (h2 : n ≤ 1000) :
  check_sum_of_primes n 1 = is_prime n := sorry

theorem check_sum_of_primes_k2_even (n : Nat)
  (h1 : n ≥ 4) (h2 : n ≤ 1000) (h3 : n % 2 = 0) :
  check_sum_of_primes n 2 = 1 := sorry
-- </vc-theorems>