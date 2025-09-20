-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def seriesSumSolver (n : Nat) : String :=
sorry

def squaredSum (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem series_sum_solver_returns_valid_name (n : Nat)
    (h : 1 ≤ n ∧ n ≤ 1000000) :
    seriesSumSolver n = "Ravi" ∨ seriesSumSolver n = "Jhon" :=
sorry

theorem series_sum_solver_alternates (n : Nat)
    (h : 1 ≤ n ∧ n ≤ 10000) :
    (seriesSumSolver n = "Ravi" ↔ squaredSum n % 2 = 0) :=
sorry

theorem series_sum_solver_consistent (n : Nat)
    (h : 1 ≤ n ∧ n ≤ 1000000) :
    seriesSumSolver n = seriesSumSolver n :=
sorry

theorem series_sum_solver_works_on_edge_cases_1 :
    seriesSumSolver 1 = "Ravi" ∨ seriesSumSolver 1 = "Jhon" :=
sorry

theorem series_sum_solver_works_on_edge_cases_2 :
    seriesSumSolver 2 = "Ravi" ∨ seriesSumSolver 2 = "Jhon" :=
sorry

theorem series_sum_solver_works_on_edge_cases_3 :
    seriesSumSolver 1000000 = "Ravi" ∨ seriesSumSolver 1000000 = "Jhon" :=
sorry
-- </vc-theorems>