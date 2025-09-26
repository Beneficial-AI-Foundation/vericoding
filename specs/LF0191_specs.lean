-- <vc-preamble>
def is_prime (n : Int) : Prop :=
  n > 1 ∧ ∀ k, 2 ≤ k → k < n → ¬(n % k = 0)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_of_prime_factors (n : Int) : Int :=
  sorry

def pow (base exp : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_prime_factors_positive {n : Int} (h : n ≥ 2) :
  sum_of_prime_factors n > 0 ∧ sum_of_prime_factors n ≤ n :=
sorry

theorem sum_prime_factors_nonpositive {n : Int} (h : n ≤ 1) :
  sum_of_prime_factors n = 0 :=
sorry

theorem sum_prime_factors_of_prime {n : Int} (h : is_prime n) :
  sum_of_prime_factors n = n :=
sorry

theorem sum_prime_factors_of_prime_power {p k : Int}
  (hp : is_prime p) (hk : k > 0) :
  sum_of_prime_factors (pow p k) = p :=
sorry

theorem sum_prime_factors_of_product {a b : Int} (ha : a ≥ 2) (hb : b ≥ 2) :
  sum_of_prime_factors (a * b) ≤ sum_of_prime_factors a + sum_of_prime_factors b :=
sorry
-- </vc-theorems>