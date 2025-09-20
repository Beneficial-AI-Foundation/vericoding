-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_spending (initial_burles : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_spending_ge_input (initial_burles : Nat) :
  max_spending initial_burles ≥ initial_burles := by
  sorry

theorem max_spending_eq_input_when_small (initial_burles : Nat) 
  (h : initial_burles < 10) :
  max_spending initial_burles = initial_burles := by
  sorry

theorem max_spending_nat_valued (initial_burles : Nat) :
  max_spending initial_burles ≥ 0 := by
  sorry

theorem max_spending_growth (initial_burles : Nat)
  (h : initial_burles ≥ 10) :
  max_spending (initial_burles + 10) ≥ max_spending initial_burles + 11 := by
  sorry

theorem max_spending_upper_bound (initial_burles : Nat)
  (h : initial_burles > 0) :
  max_spending initial_burles ≤ initial_burles * 10 / 9 + 10 := by
  sorry
-- </vc-theorems>