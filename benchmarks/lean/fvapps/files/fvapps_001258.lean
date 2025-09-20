-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) : Nat :=
  sorry

-- Even and non-negative output for valid input
-- </vc-definitions>

-- <vc-theorems>
theorem solve_positive_even {n : Nat} (h : n ≥ 2) : 
  solve n ≥ 0 ∧ solve n % 2 = 0 :=
sorry

-- Monotonically increasing for n ≥ 4

theorem solve_monotonic {n : Nat} (h : n ≥ 4) :
  solve n ≥ solve (n - 2) :=
sorry

-- Special case for doubled perfect squares

theorem solve_perfect_squares {n : Nat} :
  ∀ x, n = 2 * (x * x) → solve n = 2 * x :=
sorry
-- </vc-theorems>