-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) : Nat := sorry

theorem solve_positive (n : Nat) (h : n > 0) : solve n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_small_values :
  solve 1 = 1 ∧ solve 2 = 2 ∧ solve 3 = 5 := sorry 

theorem solve_monotonic (n : Nat) (h : n > 1) : solve n > solve (n-1) := sorry
-- </vc-theorems>