-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def binomial_sum_coefficients (n : Nat) : List Nat := sorry

theorem binomial_sum_coefficients_length (n : Nat) :
  (binomial_sum_coefficients n).length = n + 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem binomial_sum_coefficients_first (n : Nat) :
  (binomial_sum_coefficients n).head! = 1 := sorry

theorem binomial_sum_coefficients_powers_of_two (n : Nat) (i : Nat) :
  i ≤ n → 
  (binomial_sum_coefficients n).get! i = 2^i := sorry

theorem binomial_sum_coefficients_last (n : Nat) :
  (binomial_sum_coefficients n).getLast! = 2^(n+1) - 1 := sorry
-- </vc-theorems>