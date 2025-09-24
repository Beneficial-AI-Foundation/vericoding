-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def summation_of_primes (n : Nat) : Nat := sorry

theorem summation_increases (n : Nat) (h : n ≥ 2) : 
  summation_of_primes n ≥ summation_of_primes (n-1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_less_than_square (n : Nat) (h : n ≥ 2) :
  summation_of_primes n < n * n := sorry

theorem known_small_values :
  summation_of_primes 2 = 2 ∧ 
  summation_of_primes 3 = 5 ∧
  summation_of_primes 5 = 10 := sorry

theorem sum_is_positive (n : Nat) (h : n ≥ 2) :
  summation_of_primes n > 0 := sorry
-- </vc-theorems>