-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Int) : Bool :=
sorry

def reverse_num (n : Int) : Int :=
sorry

def sq_cub_rev_prime (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_prime_basic_cases :
  ¬is_prime 1 ∧ is_prime 2 ∧ ¬is_prime 4 ∧ is_prime 5 :=
sorry

theorem is_prime_nonpositive (n : Int) :
  n ≤ 0 → ¬is_prime n :=
sorry

theorem is_prime_no_small_divisors {n : Int} (h1 : 2 ≤ n) (h2 : n ≤ 1000) :
  is_prime n → ∀ i : Int, 2 ≤ i ∧ i * i ≤ n → ¬(i ∣ n) :=
sorry

theorem sq_cub_rev_prime_properties (n : Int) (h : 1 ≤ n ∧ n ≤ 39) :
  sq_cub_rev_prime n > 0 ∧
  sq_cub_rev_prime n = sq_cub_rev_prime n :=
sorry
-- </vc-theorems>