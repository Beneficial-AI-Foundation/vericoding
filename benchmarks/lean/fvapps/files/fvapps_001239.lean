-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_sum_two_semiprimes (n : Nat) : Bool := sorry

-- Result must be a boolean
-- </vc-definitions>

-- <vc-theorems>
theorem can_sum_two_semiprimes_returns_bool (n : Nat) : 
  n ≥ 4 → n ≤ 200 → can_sum_two_semiprimes n = true ∨ can_sum_two_semiprimes n = false := sorry

-- Function can be called without error on valid inputs 

theorem can_sum_two_semiprimes_well_defined (n : Nat) :
  n ≥ 4 → n ≤ 200 → can_sum_two_semiprimes (n-1).succ = can_sum_two_semiprimes n := sorry

-- Function can be called on n+1 if it can be called on n

theorem can_sum_two_semiprimes_next (n : Nat) :
  n ≥ 4 → n ≤ 199 → can_sum_two_semiprimes n → can_sum_two_semiprimes (n+1) = true ∨ can_sum_two_semiprimes (n+1) = false := sorry

-- Function can be called on n-1 if it can be called on n and n > 4

theorem can_sum_two_semiprimes_prev (n : Nat) :
  n > 4 → n ≤ 200 → can_sum_two_semiprimes n → can_sum_two_semiprimes (n-1) = true ∨ can_sum_two_semiprimes (n-1) = false := sorry
-- </vc-theorems>