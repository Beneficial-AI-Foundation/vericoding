-- <vc-preamble>
def MOD := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_series (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_series_increases (n : Nat) (h : n > 0) (h2 : n ≤ 100) :
  solve_series (n+1) > solve_series n :=
sorry

theorem solve_series_one :
  solve_series 1 = 1 :=
sorry

theorem solve_series_large_bound (n : Nat) (h : n = 1000000) :
  solve_series n < MOD :=
sorry
-- </vc-theorems>