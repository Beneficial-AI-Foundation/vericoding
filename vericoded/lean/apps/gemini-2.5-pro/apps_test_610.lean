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
theorem OptimalVasyaScore_eq_min (n m : Int) (h : ValidInput n m) :
  OptimalVasyaScore n m h = min n m := by
  unfold OptimalVasyaScore
  rw [min_def]
  rcases lt_trichotomy n m with h_lt | rfl | h_gt
  · simp [h_lt, le_of_lt h_lt]
  · simp
  · simp [not_lt_of_gt h_gt, not_le_of_gt h_gt]

-- LLM HELPER
theorem OptimalPetyaScore_eq_max_sub_one (n m : Int) (h : ValidInput n m) :
  OptimalPetyaScore n m h = max n m - 1 := by
  unfold OptimalPetyaScore
  rw [OptimalVasyaScore_eq_min n m h]
  have h_add : n + m = min n m + max n m := (min_add_max n m).symm
  rw [h_add]
  abel

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
  unfold solve_postcond solve
  simp
  unfold OptimalPetyaScore TotalAdjacentPairs
  abel
-- </vc-theorems>
