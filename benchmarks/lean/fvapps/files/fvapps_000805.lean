-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_barbecue_sticks (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bbq_sticks_positive (n: Nat) (h: n ≥ 3): 
  solve_barbecue_sticks n > 0 :=
  sorry

theorem bbq_sticks_odd (n: Nat) (h: n ≥ 3):
  solve_barbecue_sticks n % 2 = 1 :=
  sorry 

theorem bbq_sticks_exponential_growth (n: Nat) (h: n ≥ 3):
  solve_barbecue_sticks n ≥ 2^(n-2) :=
  sorry

theorem bbq_sticks_strictly_increasing {n: Nat} (h: n > 3):
  solve_barbecue_sticks n > solve_barbecue_sticks (n-1) :=
  sorry
-- </vc-theorems>