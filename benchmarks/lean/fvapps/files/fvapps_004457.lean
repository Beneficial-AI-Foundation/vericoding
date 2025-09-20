-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zeros (n : Nat) : Nat := sorry

theorem zeros_non_negative (n : Nat) :
  zeros n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zeros_monotonic (n : Nat) :
  n > 0 → zeros n ≥ zeros (n-1) := sorry

theorem zeros_less_than_input (n : Nat) :
  n > 0 → zeros n < n := sorry

theorem zeros_small_inputs :
  zeros 0 = 0 ∧ zeros 1 = 0 ∧ zeros 4 = 0 := sorry
-- </vc-theorems>