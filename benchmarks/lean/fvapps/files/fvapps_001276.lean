-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_series (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_series_output_type {n : Nat} (h : n ≥ 1) :
  solve_series n ≥ 0 :=
sorry

theorem solve_series_base_case :
  solve_series 1 = 0 :=
sorry

theorem solve_series_strictly_increasing {n : Nat} (h : n ≥ 2) :
  solve_series n < solve_series (n + 1) :=
sorry

theorem solve_series_formula {n : Nat} (h : n ≥ 2) :
  solve_series n = ((n - 2 + 1) * (2 * (n - 2) + 3) * (n - 2 + 2)) / 6 :=
sorry
-- </vc-theorems>