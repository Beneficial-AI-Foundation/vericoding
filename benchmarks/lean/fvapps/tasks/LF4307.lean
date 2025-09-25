-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factor_sum (n : Nat) : Nat := sorry 

def sum_of_prime_factors (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem factor_sum_positive {n : Nat} (h : n ≥ 2) :
  factor_sum n > 0 := sorry

theorem factor_sum_idempotent {n : Nat} (h : n ≥ 2) :
  factor_sum (factor_sum n) = factor_sum n := sorry
-- </vc-theorems>