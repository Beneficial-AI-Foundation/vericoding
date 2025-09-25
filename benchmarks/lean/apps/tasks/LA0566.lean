-- <vc-preamble>
def ValidInput (test_cases : List (Int × Int)) : Prop :=
  ∀ i, 0 ≤ i ∧ i < test_cases.length → 
      test_cases[i]!.1 > 0 ∧ test_cases[i]!.2 > 0

def MinMovesToDivisible (a b : Int) : Int :=
  if a > 0 ∧ b > 0 then (b - a % b) % b else 0

def ValidOutput (test_cases : List (Int × Int)) (results : List Int) : Prop :=
  ValidInput test_cases →
  results.length = test_cases.length ∧
  ∀ i, 0 ≤ i ∧ i < results.length → 
      results[i]! = MinMovesToDivisible test_cases[i]!.1 test_cases[i]!.2 ∧
      results[i]! ≥ 0

@[reducible, simp]
def solve_precond (test_cases : List (Int × Int)) : Prop :=
  ValidInput test_cases
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (test_cases : List (Int × Int)) (h_precond : solve_precond test_cases) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (test_cases : List (Int × Int)) (results : List Int) (h_precond : solve_precond test_cases) : Prop :=
  ValidOutput test_cases results

theorem solve_spec_satisfied (test_cases : List (Int × Int)) (h_precond : solve_precond test_cases) :
    solve_postcond test_cases (solve test_cases h_precond) h_precond := by
  sorry
-- </vc-theorems>