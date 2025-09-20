-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagonal (n : Nat) (p : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_nonnegative (n p : Nat) :
  diagonal n p ≥ 0 :=
  sorry

theorem diagonal_p_greater_n (n p : Nat) :
  p > n → diagonal n p = 0 :=
  sorry

theorem diagonal_p_zero (n : Nat) :
  diagonal n 0 = n + 1 :=
  sorry

theorem diagonal_monotone_n (n p : Nat) :
  n > 0 → p ≤ n → diagonal n p ≥ diagonal (n-1) p :=
  sorry 

theorem diagonal_positive_small_values (n p : Nat) :
  p ≤ n → diagonal n p > 0 :=
  sorry
-- </vc-theorems>