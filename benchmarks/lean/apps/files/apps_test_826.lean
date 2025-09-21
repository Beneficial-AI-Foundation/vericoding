-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def IsOptimalSavings (n : Int) (savings : Int) : Prop :=
  n ≥ 1 →
  savings ≥ 0 ∧
  (2 + savings) * (savings + 1) / 2 > n + 1 ∧
  (savings = 0 ∨ (2 + (savings - 1)) * savings / 2 ≤ n + 1)

def IsMinimalSavings (n : Int) (savings : Int) : Prop :=
  n ≥ 1 →
  IsOptimalSavings n savings ∧
  (∀ j, j ≥ 0 ∧ j < savings → (2 + j) * (j + 1) / 2 ≤ n + 1)

def OptimalCost (n : Int) (savings : Int) : Int :=
  n - savings + 1

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result ≥ 1 ∧
  result ≤ n ∧
  ∃ savings, IsMinimalSavings n savings ∧ result = OptimalCost n savings

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>