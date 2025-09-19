-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n: Nat) : Nat := sorry

theorem solve_returns_positive (n: Nat) (h: n ≥ 2) : 
  solve n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_less_than_sum (n: Nat) (h: n ≥ 2) :
  solve n ≤ (n * (n + 1)) / 2 := sorry

theorem solve_monotonic (n: Nat) (h: n ≥ 2) :
  solve n ≤ solve (n + 1) := sorry

theorem solve_base_cases :
  solve 2 = 3 ∧ solve 3 = 6 ∧ solve 4 = 6 := sorry
-- </vc-theorems>