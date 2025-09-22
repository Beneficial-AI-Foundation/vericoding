-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def halving_sum (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem halving_sum_lower_bound (n : Nat) (h : n > 0) :
  halving_sum n ≥ n :=
sorry

theorem halving_sum_upper_bound (n : Nat) (h : n > 0) :
  halving_sum n < 2*n :=
sorry

theorem halving_sum_power_of_two (n : Nat) (h : n > 0)
  (h_pow : ∃ k, n = 2^k) :
  halving_sum n = 2*n - 1 :=
sorry

theorem halving_sum_base_cases :
  (halving_sum 1 = 1) ∧ (halving_sum 2 = 3) :=
sorry
-- </vc-theorems>