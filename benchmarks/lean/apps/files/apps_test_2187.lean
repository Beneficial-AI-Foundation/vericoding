-- <vc-preamble>
def ValidInput (test_cases : List (List Int)) : Prop :=
  ∀ i, 0 ≤ i ∧ i < test_cases.length → test_cases[i]!.length ≥ 1

def SumDifferences (arr : List Int) (start : Nat) : Int :=
  if start ≥ arr.length - 1 then 0
  else (if arr[start]! > arr[start + 1]! then arr[start]! - arr[start + 1]! else 0) + SumDifferences arr (start + 1)

def CorrectResult (test_cases : List (List Int)) (results : List Int) : Prop :=
  results.length = test_cases.length ∧
  (∀ i, 0 ≤ i ∧ i < test_cases.length → results[i]! = SumDifferences test_cases[i]! 0) ∧
  (∀ i, 0 ≤ i ∧ i < results.length → results[i]! ≥ 0)

@[reducible, simp]
def solve_precond (test_cases : List (List Int)) : Prop :=
  ValidInput test_cases
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (test_cases : List (List Int)) (h_precond : solve_precond test_cases) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (test_cases : List (List Int)) (results : List Int) (h_precond : solve_precond test_cases) : Prop :=
  CorrectResult test_cases results

theorem solve_spec_satisfied (test_cases : List (List Int)) (h_precond : solve_precond test_cases) :
    solve_postcond test_cases (solve test_cases h_precond) h_precond := by
  sorry
-- </vc-theorems>