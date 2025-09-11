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

/-
info: 17
-/
-- #guard_msgs in
-- #eval summation_of_primes 10

/-
info: 77
-/
-- #guard_msgs in
-- #eval summation_of_primes 20

/-
info: 1060
-/
-- #guard_msgs in
-- #eval summation_of_primes 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible