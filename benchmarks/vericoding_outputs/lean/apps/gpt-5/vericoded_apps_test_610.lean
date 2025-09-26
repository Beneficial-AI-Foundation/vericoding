import Mathlib
-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1

def OptimalVasyaScore (n m : Int) (h : ValidInput n m) : Int :=
  if n < m then n else m

def OptimalPetyaScore (n m : Int) (h : ValidInput n m) : Int :=
  n + m - 1 - OptimalVasyaScore n m h

def TotalAdjacentPairs (n m : Int) (h : ValidInput n m) : Int :=
  n + m - 1

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers required for this problem.
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int × Int :=
  (OptimalPetyaScore n m h_precond, OptimalVasyaScore n m h_precond)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int × Int) (h_precond : solve_precond n m) : Prop :=
  result.2 = OptimalVasyaScore n m h_precond ∧ 
  result.1 = OptimalPetyaScore n m h_precond ∧ 
  result.1 + result.2 = TotalAdjacentPairs n m h_precond

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  constructor
  · simp [solve, solve_postcond]
  · constructor
    · simp [solve, solve_postcond]
    · simp [solve, solve_postcond, OptimalPetyaScore, TotalAdjacentPairs]
-- </vc-theorems>
