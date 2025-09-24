-- <vc-preamble>
def ValidInput (testCases : List (Int × Int)) : Prop :=
  ∀ i, 0 ≤ i ∧ i < testCases.length → 
    0 ≤ testCases[i]!.1 ∧ testCases[i]!.1 < 24 ∧ 
    0 ≤ testCases[i]!.2 ∧ testCases[i]!.2 < 60 ∧ 
    ¬(testCases[i]!.1 = 0 ∧ testCases[i]!.2 = 0)

def MinutesUntilMidnight (h m : Int) : Int :=
  1440 - (h * 60 + m)

def ValidOutput (results : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < results.length → 1 ≤ results[i]! ∧ results[i]! ≤ 1439

@[reducible, simp]
def solve_precond (testCases : List (Int × Int)) : Prop :=
  ValidInput testCases
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (testCases : List (Int × Int)) (h_precond : solve_precond testCases) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (testCases : List (Int × Int)) (results : List Int) (h_precond : solve_precond testCases) : Prop :=
  results.length = testCases.length ∧ 
  (∀ i, 0 ≤ i ∧ i < results.length → results[i]! = MinutesUntilMidnight testCases[i]!.1 testCases[i]!.2) ∧
  ValidOutput results

theorem solve_spec_satisfied (testCases : List (Int × Int)) (h_precond : solve_precond testCases) :
    solve_postcond testCases (solve testCases h_precond) h_precond := by
  sorry
-- </vc-theorems>